/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import IrisFix.BI.Lib.Fixpoint
public meta import IrisFix.ProofMode.Lib.Monotone
public meta import Lean.Compiler.NoncomputableAttr
public meta import IrisFix.Std.Meta

/-! # `ifix` and `icofix`

`ifix name binders : type := body` defines `name := bind₂ name name.pre` by `partial_fixpoint`, on
downsets of `PROP` in the order of `MonotoneFixpoint` (`icofix`: `CoMonotoneFixpoint`), where
`name.pre := fun name binders => body`. The definition is monotone for every body. The tactic proves
`IMono PROP name.pre`; then `name` is the fixpoint of `name.pre`, read from `partial_fixpoint`'s own
`name.fixpoint_induct` and `name.eq_unfold`, and the laws are the generic laws of `IsFix`. Their
statements unfold the `IOrder` instances, so they quantify over the parameters, curried. Every
binder is a parameter of the fixpoint, except leading instance binders and implicit binders that
the result type mentions: like section variables, they are parameters of the definition. Generated
declarations of a protected `name` are protected. -/

public section

namespace Iris.Fixpoint
open Lean Elab Command Term Meta BI Iris.Meta

syntax monotoneClause := "monotone_by " Lean.Parser.Tactic.tacticSeq

/-- The default monotonicity tactic of `ifix` and `icofix`, on the goal `IOrder.IMono PROP F`. It is
`imono`; extend it with `macro_rules`. -/
syntax "ifix_monotone_default" : tactic
macro_rules | `(tactic| ifix_monotone_default) => `(tactic| imono)

/-- The statement of a law: `e`, with the orders unfolded, and default values and auto-params
dropped. -/
meta def cleanup (e : Expr) : MetaM Expr := do
  Core.betaReduce <| ← unfoldOrders <| e.replace fun e =>
    if e.isAppOfArity ``optParam 2 || e.isAppOfArity ``autoParam 2 then some (e.getArg! 0)
    else none

/-- Unfold the orders of `IOrder` in the goal, into the BI. -/
elab "ifix_unfold" : tactic => Tactic.liftMetaTactic1 fun g => do
  g.replaceTargetDefEq (← unfoldOrders (← g.getType))

/-- Add `declName.pre := fun params => G`, exposed and compiled like a definition. -/
meta def emitPre (declName : Name) (levels : List Name) (params : Array Expr) (G : Expr) :
    MetaM Expr := do
  let name := declName ++ `pre
  let type ← instantiateMVars (← mkForallFVars params (← inferType G))
  let value ← instantiateMVars (← mkLambdaFVars params G)
  let decl := Declaration.defnDecl
    { name, levelParams := levels, type, value, hints := .abbrev, safety := .safe }
  addDecl decl (forceExpose := true)
  setReducibilityStatus name .reducible
  if isNoncomputable (← getEnv) declName then modifyEnv (addNoncomputable · name)
  else compileDecl decl (logErrors := false)
  enableRealizationsForConst name
  if isProtected (← getEnv) declName then modifyEnv (addProtected · name)
  return mkAppN (.const name (levels.map mkLevelParam)) params

/-- Emit `declName.unfold : ∀ binders, fn args = pre fn args`, from `eq : fn = pre fn`, at the
arguments `args`, and `unfold_mp` and `unfold_mpr`, its two entailments. -/
meta def emitUnfold (declName : Name) (levels : List Name) (binders args : Array Expr)
    (eq fn pre : Expr) : MetaM Unit := do
  let value ← args.foldlM mkCongrFun eq
  let (lhs, rhs) := ((mkAppN fn args).headBeta, mkAppN (mkApp pre fn) args)
  let emit (suffix : Name) (type value : Expr) := do
    emitThm (declName ++ suffix) levels (← mkForallFVars binders type)
      (← mkLambdaFVars binders value)
  emit `unfold (← mkEq lhs rhs) value
  -- If the values are in a BI.
  let some mp ← observing? (mkAppM ``BIBase.Entails.of_eq #[value]) | return
  emit `unfold_mp (← mkAppM ``BIBase.Entails #[lhs, rhs]) mp
  emit `unfold_mpr (← mkAppM ``BIBase.Entails #[rhs, lhs])
    (← mkAppM ``BIBase.Entails.of_eq #[← mkEqSymm value])

/-- `B`, up to reducible definitions (such as an `abbrev` that drops a parameter); it must not
depend on `xs`. -/
meta def baseType (xs : Array Expr) (B : Expr) : MetaM Expr := do
  let B ← withReducible <| reduce B (explicitOnly := false) (skipTypes := false)
  if B.hasAnyFVar (xs.contains <| .fvar ·) then
    throwError "the result type{indentExpr B}\ndepends on the parameters"
  return B

/-- `fix_bind% (∀ xs, X) k`, in a recursive definition of type `∀ xs, D`, where `D` approximates
`X`: `bind₂ name k`, the definition approximating the body `k : (∀ xs, X) → ∀ xs, X`. -/
syntax (name := fixBind) "fix_bind% " term:max term:max : term

@[term_elab fixBind] meta def elabFixBind : TermElab := fun stx expectedType? => do
  let `(fix_bind% $PX $k) := stx | throwUnsupportedSyntax
  let some E := expectedType? | throwError "fix_bind%: the expected type is unknown"
  let E ← instantiateMVars E
  let arity ← forallTelescopeReducing E fun xs _ => return xs.size
  -- `D`, `X`, and `∀ xs, X`, over the binders of `E`.
  let (D, X, PX) ← forallBoundedTelescope E arity fun xs D => do
    let X ← instantiateForall (← elabType PX) xs
    return (← baseType xs D, ← baseType xs X, ← mkForallFVars xs X)
  -- The definition, at its parameters: by unification with `E`, and instances.
  let some name := (((← getLCtx).decls.toArray.filterMap id).filter (·.isAuxDecl)).back?
    | throwError "fix_bind%: not in a recursive definition"
  let n := (← forallTelescopeReducing name.type fun xs _ => return xs.size) - arity
  let (ms, _, ty) ← forallMetaBoundedTelescope name.type n
  unless ← isDefEq ty E do throwError "fix_bind%: unexpected type{indentExpr name.type}"
  for m in ms do
    unless ← m.mvarId!.isAssigned do m.mvarId!.assign (← synthInstance (← inferType m))
  let fn ← instantiateMVars (mkAppN name.toExpr ms)
  let k ← elabTermEnsuringType k (← mkArrow PX PX)
  mkAppOptM ``bind₂ #[D, X, none, E, PX, none, none, none, fn, k]

/-- A `partial_fixpoint` `name := bind₂ name body`: its fixed parameters, the order `X` of the
fixpoint and its instance, the fixpoint `fn`, the `body`, with explicit binders, and
`isFix : IsFix (bind₂ · body) fn`. The fixed parameters are section variables where they can be. -/
meta structure FixInfo where
  fixed : Array Expr
  X : Expr
  inst : Expr
  fn : Expr
  body : Expr
  isFix : Expr

/-- Read the `partial_fixpoint` `declName` from its `fixpoint_induct` and `eq_unfold`, in the
context of the section variables `vars`. -/
meta def readFix {α} (declName : Name) (us : List Level) (vars : Array Expr)
    (k : FixInfo → TermElabM α) : TermElabM α := do
  let (induct, eqUnfold) := (declName ++ `fixpoint_induct, declName ++ `eq_unfold)
  executeReservedNameAction induct
  executeReservedNameAction eqUnfold
  -- `∀ fixed (motive : X → Prop), admissible motive → (∀ f, motive f → motive (F f)) → motive fn`
  let type ← inferType (.const induct us)
  let n := (← forallTelescope type fun xs _ => return xs.size) - 3
  forallBoundedTelescope type n fun xs rest => withSectionVars vars xs fun fixed => do
  forallTelescope (rest.replaceFVars xs fixed) fun xs concl => do
    let_expr Lean.Order.admissible X inst _ := ← inferType xs[1]!
      | throwError "unexpected{indentExpr type}"
    let fn := concl.appArg!
    let F ← forallTelescope (← inferType xs.back!) fun fs step =>
      mkLambdaFVars #[fs[0]!] step.appArg!
    -- `fn = F fn`: `eq_unfold`, at `fn`.
    let unfold ← withLocalDeclD `f (← inferType (.const declName us)) fun f => do
      mkCongrArg (← mkLambdaFVars #[f] (fn.replace (if ·.isConstOf declName then f else none)))
        (.const eqUnfold us)
    let isFix ← mkAppOptM ``IsFix.mk #[X, inst, F, fn, mkAppN (.const induct us) fixed, unfold]
    -- `F = fun f => bind₂ f body`; the laws quantify over the parameters, explicitly.
    let explicit (e : Expr) := e.replace fun
      | .lam x t b _ => some (.lam x t b .default)
      | .forallE x t b _ => some (.forallE x t b .default)
      | _ => none
    k { fixed, X := explicit X, inst, fn, body := explicit F.bindingBody!.appArg!, isFix }

/-- The parameters of the laws: `fixed`, and the section variables of `vars` that the proof `h`
uses. -/
meta def lawParams (fixed vars : Array Expr) (h : Expr) : Array Expr :=
  fixed ++ vars.filter fun v => !fixed.contains v && h.containsFVar v.fvarId!

/-- Emit `name.pre`, `name.pre_mono`, `name.unfold` and the laws of `name := bind₂ name k`. `tac`
proves `IMono PROP k`; then `bind₂ · k = k`, and `name` is the fixpoint of `name.pre := k`.
`coind` names the laws for the greatest fixpoint. The laws take the section variables of `vars`
that the proof of `tac` uses. -/
meta def emitLaws (declName : Name) (coind : Bool) (tac : Syntax) (vars : Array Expr) :
    TermElabM Unit := do
  let info ← getConstInfoDefn declName
  -- The definition failed: the errors are already reported.
  if info.value.hasSorry then return
  checkFresh declName <| [`pre, `pre_mono, `unfold, `unfold_mp, `unfold_mpr, `strong_mono, `ne] ++
    if coind then [`coiter, `coind, `paco, `absorbing]
    else [`iter, `ind, `ind_wf, `affine, `absorbing, `persistent_affine, `persistent_absorbing]
  let levels := info.levelParams
  readFix declName (levels.map mkLevelParam) vars fun { fixed, X, inst, fn, body, isFix } => do
    let PROP ← forallTelescopeReducing X fun _ P => return P
    let some hF ← proveBy tac (← mkAppM ``IOrder.IMono #[PROP, body]) | return
    let params := lawParams fixed vars hF
    let pre ← emitPre declName levels fixed body
    -- A monotone body runs on the fixpoint: `name` is the fixpoint of `name.pre`.
    let hm ← mkAppM ``IOrder.monotone_of_imono #[hF]
    let isFix ← mkExpectedTypeHint (← mkAppM ``IsFix.of_bind₂_downset #[isFix, hm])
      (← mkAppOptM ``IsFix #[X, inst, pre, fn])
    -- `name.unfold`, quantified like `name`, and the names that law binders avoid.
    let unfold ← mkAppM ``IsFix.unfold #[isFix]
    let avoid ← forallTelescopeReducing X fun ys _ => do
      emitUnfold declName levels (params ++ ys) ys unfold fn pre
      ys.toList.mapM (·.fvarId!.getUserName)
    -- The law `value`, over the parameters and the section variables it uses; its first `hyps`
    -- hypotheses are instance arguments.
    let emit (suffix : Name) (value : Expr) (hyps : Nat := 0) : MetaM Unit := do
      let type ← cleanup (← lawType avoid value)
      let type ← forallBoundedTelescope type hyps fun hs b => do
        withNewBinderInfos (hs.map (·.fvarId!, .instImplicit)) (mkForallFVars hs b)
      let ps := lawParams params vars value
      emitThm (declName ++ suffix) levels (← mkForallFVars ps type) (← mkLambdaFVars ps value)
    emitThm (declName ++ `pre_mono) levels
      (← mkForallFVars params (← unfoldOrders (← mkAppM ``IOrder.IMono #[PROP, pre])))
      (← mkLambdaFVars params hF)
    -- The generic laws, at `name.pre` and `name`.
    let law (lemma : Name) := mkAppM lemma #[isFix, hF]
    emit (if coind then `coiter else `iter) (← law ``IsFix.iter)
    emit `strong_mono (← law ``IsFix.strong_mono)
    emit (if coind then `coind else `ind) (← law ``IsFix.ind)
    emit (if coind then `paco else `ind_wf) (← law ``IsFix.ind_wf)
    -- `ne`, if an argument has an OFE.
    let ineType := mkApp2 (← mkConstWithFreshMVarLevels ``INe) X inst
    if let some ine ← observing? (synthInstance ineType) then
      if (ine.find? (·.isConstOf ``INe.instPiNE)).isSome then
        emit `ne (← mkAppM ``IsFix.ne #[isFix, hm])
    -- The instances: the generic theorems, with their hypotheses as instance arguments.
    let inst (suffix lemma : Name) (hyps : Nat) : MetaM Unit := do
      emit suffix (← mkAppM lemma #[PROP, isFix, hm]) hyps
      addInstance (declName ++ suffix) .global (eval_prio default)
    if coind then
      inst `absorbing ``IsFix.gfp_absorbing 1
    else
      inst `affine ``IsFix.lfp_affine 1
      inst `absorbing ``IsFix.lfp_absorbing 1
      inst `persistent_affine ``IsFix.lfp_persistent_affine 2
      inst `persistent_absorbing ``IsFix.lfp_persistent_absorbing 2

/-- `name binders : type := body`, or with match alternatives: the declaration of a fixpoint. -/
syntax fixDecl := ppIndent(declId Lean.Parser.Command.optDeclSig
  ((" := " term) <|> Lean.Parser.Term.matchAltsWhereDecls))

/-- A `fixDecl`: its `name`, the full name `full`, the binders `params` of the definition and
`binders` of the fixpoint (`_` named), the result type `ty`, and the `body`, a term. -/
meta structure FixDecl where
  id : TSyntax ``Lean.Parser.Command.declId
  name : Ident
  full : Name
  params : Array Syntax
  binders : Array Syntax
  ty : Term
  body : Term

/-- The leading instance binders, and implicit binders that the result type `ty` mentions, are
parameters of the definition, like the section variables; the other binders are the parameters of
the fixpoint. -/
meta def splitBinders (bs : Array Syntax) (ty : Syntax) : Array Syntax × Array Syntax :=
  let inTy (x : Syntax) := (ty.find? fun s => s.isIdent && s.getId == x.getId).isSome
  let fixed (b : Syntax) := b.getKind == ``Lean.Parser.Term.instBinder ||
    ((b.getKind == ``Lean.Parser.Term.implicitBinder ||
      b.getKind == ``Lean.Parser.Term.strictImplicitBinder) && b[1].getArgs.any inTy)
  let n := (bs.toList.takeWhile fixed).length
  (bs.extract 0 n, bs.extract n)

/-- Read the `fixDecl` `stx` of the command `cmd`. -/
meta def FixDecl.read (cmd : String) (stx : Syntax) : CommandElabM FixDecl := do
  let #[id, sig, body] := stx.getArgs | throwUnsupportedSyntax
  let some ty := sig[1].getOptional? | throwErrorAt sig "{cmd}: the type of the fixpoint is needed"
  let ty : Term := ⟨ty[1]⟩
  let body : Term ← if body[0].isAtom then pure ⟨body[1]⟩ else
    -- `matchAltsWhereDecls`: alternatives, termination hints, and `where` declarations.
    unless body[1][0].isNone && body[1][1].isNone && body[2].isNone do
      throwErrorAt body "{cmd}: the body takes no termination hints or `where` declarations"
    `(fun $(⟨body[0]⟩):matchAlts)
  let name : Ident := ⟨id[0]⟩
  let (params, binders) := splitBinders (← nameHoles sig[0].getArgs) ty
  return { id := ⟨id⟩, name, full := ← fullName name.getId, params, binders, ty, body }

/-- `params`, as binders. -/
meta def FixDecl.paramBinders (d : FixDecl) : TSyntaxArray ``Lean.Parser.Term.bracketedBinder :=
  d.params.map (⟨·⟩)

/-- `fix_bind% (∀ binders, ty) (fun (self : ∀ binders, ty) => fun binders => body)`, where the
references to the declaration, written `name`, are `self`. A parameter named `name` shadows it,
as in Lean. -/
meta def FixDecl.value (d : FixDecl) : CommandElabM Term := do
  let self : Ident := ⟨(← `(self)).raw⟩
  let shadowed := d.binders.any fun b => b[1].getArgs.any (·.getId == d.name.getId)
  let parts := (d.name.getId.replacePrefix `_root_ .anonymous).getNumParts
  let body ← d.body.raw.replaceM fun s => pure do
    let x := s.getId.replacePrefix `_root_ .anonymous
    guard (s.isIdent && x.isSuffixOf d.full && x.getNumParts ≥ parts)
    guard !(shadowed && s.getId == d.name.getId)
    return self
  let sig ← forallStx d.binders d.ty
  `(no_implicit_lambda% (fix_bind% $sig
    (fun ($self : $sig) => no_implicit_lambda% $(← funStx d.binders ⟨body⟩))))

/-- `ifix name binders : type := body`: the least fixpoint, by `partial_fixpoint`; `icofix`: the
greatest. The body is a term or match alternatives. -/
syntax (name := ifixCmd) declModifiers ("ifix " <|> "icofix ") fixDecl
  (ppDedent(ppLine) monotoneClause)? : command

/-- `ifix`/`icofix`: `name := bind₂ name body` by `partial_fixpoint`, on downsets in the order of
`MonotoneFixpoint` (`CoMonotoneFixpoint`), and then its laws. -/
@[command_elab ifixCmd] meta def elabIfix : CommandElab := fun stx => do
  let #[mods, kw, decl, clause] := stx.getArgs | throwUnsupportedSyntax
  let coind := (kw.find? (·.getAtomVal.trimAscii == "icofix")).isSome
  let ord := if coind then `Iris.CoMonotoneFixpoint else `Iris.MonotoneFixpoint
  let d ← FixDecl.read "ifix" decl
  -- The monotonicity tactic, on `IMono PROP F`.
  let tac ← match clause.getOptional? with
    | some c => `(tactic| (ifix_unfold; $(⟨c[1]⟩)))
    | none => `(tactic| ifix_monotone_default)
  unless (← getEnv).contains d.full do liftCoreM <| checkFresh d.full [`pre, `iter, `coiter]
  withLargeInstances do
  unless ← elabDef (← `(command| open scoped $(mkIdent ord) in
      $(⟨mods⟩):declModifiers def $d.id $d.paramBinders* : $(← forallStx d.binders d.ty) :=
        $(← d.value)
      partial_fixpoint monotonicity $(mkCIdent ``bind₂_mono_downset))) do return
  let declName ← liftCoreM <| resolveDeclared d.full
  pushScope
  activateScoped ord
  try runTermElabM (emitLaws declName coind tac) finally popScope

end Iris.Fixpoint
