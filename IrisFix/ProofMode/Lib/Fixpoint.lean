/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import IrisFix.BI.Lib.Fixpoint
public meta import IrisFix.ProofMode.Lib.Monotone
public meta import Lean.Compiler.NoncomputableAttr

/-! # `ifix` and `icofix`

`ifix name binders : type := body` defines `name` by `partial_fixpoint`, in the order of
`MonotoneFixpoint` (`icofix`: `CoMonotoneFixpoint`), which also infers the fixed parameters. The
laws are the generic laws of `IsFix`, at `name.pre`, from `partial_fixpoint`'s own
`name.fixpoint_induct` and `name.eq_unfold`; the monotonicity tactic runs again, for `name.pre`.
Their statements unfold the `IOrder` instances, so they quantify over the varying parameters,
curried. Laws are emitted only if the definition succeeds. A non-recursive body is a fixpoint too;
a body without BI operations needs `local bi`. Generated declarations of a protected `name` are
protected. -/

public section

namespace Iris.Fixpoint
open Lean Elab Command Term Meta BI

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

/-- Close `monotone F` by `IOrder.monotone_of_imono`, proving `IMono PROP F` with `tac`. `PROP` is
the codomain of the domain of `F`. -/
syntax (name := ifixMonotone) "ifix_monotone " Lean.Parser.Tactic.tacticSeq : tactic

@[tactic ifixMonotone] meta def evalIfixMonotone : Tactic.Tactic
  | `(tactic| ifix_monotone $tac) => Tactic.withMainContext do
    let goal ← Tactic.getMainGoal
    let_expr Lean.Order.monotone X _ _ _ F := ← whnfR (← goal.getType)
      | throwError "ifix_monotone: expected a goal `monotone F`"
    let PROP ← forallTelescopeReducing X fun _ P => pure P
    let err := m!"ifix_monotone: the order of{indentExpr X}\nis not the order of `IOrder`"
    let imono ← try mkAppM ``IOrder.IMono #[PROP, F] catch _ => throwError err
    let hF ← mkFreshExprSyntheticOpaqueMVar imono
    let proof ← mkAppM ``IOrder.monotone_of_imono #[hF]
    unless ← isDefEq (← inferType proof) (← goal.getType) do throwError err
    goal.assign proof
    Tactic.replaceMainGoal [hF.mvarId!]
    Tactic.evalTactic tac
  | _ => throwUnsupportedSyntax

/-- Unfold the orders of `IOrder` in the goal, into the BI. -/
elab "ifix_unfold" : tactic => Tactic.liftMetaTactic1 fun g => do
  g.replaceTargetDefEq (← unfoldOrders (← g.getType))

/-- The full name of the declaration `name` in the current namespace, as `def` names it. -/
meta def fullName (name : Name) : CommandElabM Name := do
  if name.getRoot == `_root_ then return name.replacePrefix `_root_ .anonymous
  return (← getCurrNamespace) ++ name

/-- The declaration `full`, just declared, perhaps private. -/
meta def resolveDeclared (full : Name) : CoreM Name := do
  let env ← getEnv
  if env.contains full then return full
  let priv := mkPrivateName env full
  if env.contains priv then return priv
  throwError "unknown declaration `{full}`"

/-- Fail if a declaration to be generated, `declName ++ s` for `s` in `suffixes`, exists. -/
meta def checkFresh (declName : Name) (suffixes : List Name) : CoreM Unit := do
  for s in suffixes do
    if (← getEnv).contains (declName ++ s) then
      throwError "cannot generate `{declName ++ s}`: a declaration with this name already exists"

/-- Elaborate `cmd`. If it fails, undo it and return its messages. -/
meta def tryElab (cmd : Syntax) : CommandElabM (Option MessageLog) := do
  let saved := (← get).messages
  let env ← getEnv
  modify ({ · with messages := {} })
  withScope (fun sc => { sc with opts := Elab.async.set sc.opts false }) <| elabCommand cmd
  let new := (← get).messages
  if new.hasErrors then
    modify ({ · with messages := saved })
    setEnv env
    return some new
  modify ({ · with messages := saved ++ new })
  return none

/-- Report the messages of a failed definition, without duplicates. If an error lies inside the
command, drop the messages at its start: they are follow-ups, about the definition as a whole. -/
meta def reportErrors (errs : MessageLog) : CommandElabM Unit := do
  let some start := (← getRef).getPos? | return
  let start := (← getFileMap).toPosition start
  let inside (m : Message) := m.pos != start
  let msgs := errs.toList
  let msgs := if msgs.any (fun m => m.severity == .error && inside m) then msgs.filter inside
    else msgs
  let mut seen : List String := []
  for m in msgs do
    let s ← m.toString
    unless seen.contains s do
      logMessage m
      seen := s :: seen

/-- Add a theorem; the kernel checks `value` against `type`. A theorem about a protected
declaration is protected. -/
meta def emitThm (name : Name) (levels : List Name) (type value : Expr) : MetaM Unit := do
  let type ← instantiateMVars type
  let value ← instantiateMVars value
  addDecl <| .thmDecl { name, levelParams := levels, type, value }
  if isProtected (← getEnv) name.getPrefix then modifyEnv (addProtected · name)

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

/-- Prime the binders of `e` that clash with `avoid`. -/
meta partial def primeNames (avoid : List Name) (e : Expr) : Expr :=
  e.replace fun
    | .forallE x t b bi => some (.forallE (prime x) (primeNames avoid t) (primeNames avoid b) bi)
    | _ => none
where prime x := if avoid.contains x then prime (x.appendAfter "'") else x

/-- The type of the law `value`, an application of a lemma, with the binders of the lemma that
clash with `avoid` (the parameters) primed. -/
meta def lawType (avoid : List Name) (value : Expr) : MetaM Expr := do
  let type := primeNames avoid (← inferType value.getAppFn)
  instantiateMVars (← instantiateForall type value.getAppArgs)

/-- Remove `let`s whose variable is unused, such as the one that makes a non-recursive body
recursive. -/
meta partial def elimDeadLets (e : Expr) : Expr :=
  e.replace fun e => match e with
    | .letE _ _ _ b _ =>
      if b.hasLooseBVar 0 then none else some (elimDeadLets (b.lowerLooseBVars 1 1))
    | _ => none

/-- Emit `name.pre`, `name.pre_mono`, `name.unfold` and the laws of `name`, a `partial_fixpoint`,
from its `fixpoint_induct` and `eq_unfold`. `tac` proves `IMono PROP name.pre`, again. `coind`
names the laws for the greatest fixpoint. -/
meta def emitLaws (declName : Name) (coind : Bool) (tac : Syntax) : TermElabM Unit := do
  let info ← getConstInfoDefn declName
  -- The definition, or its monotonicity proof, failed: the errors are already reported.
  if info.value.hasSorry then return
  checkFresh declName <| [`pre, `pre_mono, `unfold, `unfold_mp, `unfold_mpr, `strong_mono, `ne] ++
    if coind then [`coiter, `coind, `paco, `absorbing]
    else [`iter, `ind, `ind_wf, `affine, `absorbing, `persistent_affine, `persistent_absorbing]
  let levels := info.levelParams
  let us := levels.map mkLevelParam
  let (induct, eqUnfold) := (declName ++ `fixpoint_induct, declName ++ `eq_unfold)
  executeReservedNameAction induct
  executeReservedNameAction eqUnfold
  -- `∀ fixed (motive : X → Prop), admissible motive → (∀ f, motive f → motive (F f)) → motive fn`
  forallTelescope (← inferType (.const induct us)) fun xs concl => do
    let fixed := xs.extract 0 (xs.size - 3)
    let_expr Lean.Order.admissible X inst _ := ← inferType xs[xs.size - 2]!
      | throwError "ifix: unexpected{indentExpr (← inferType (.const induct us))}"
    let fn := concl.appArg!
    let F ← forallTelescope (← inferType xs.back!) fun fs step =>
      mkLambdaFVars #[fs[0]!] step.appArg!
    -- The laws and `pre` quantify over `X`, with explicit binders.
    let X := X.replace fun | .forallE x t b _ => some (.forallE x t b .default) | _ => none
    let F := elimDeadLets <| F.replace fun | .lam x t b _ => some (.lam x t b .default) | _ => none
    let pre ← emitPre declName levels fixed F
    -- `fn = pre fn`: `eq_unfold`, at `fn`.
    let unfold ← withLocalDeclD `f (← inferType (.const declName us)) fun f => do
      mkCongrArg (← mkLambdaFVars #[f] (fn.replace (if ·.isConstOf declName then f else none)))
        (.const eqUnfold us)
    let isFix ← mkAppOptM ``IsFix.mk #[X, inst, pre, fn, mkAppN (.const induct us) fixed, unfold]
    let PROP ← forallTelescopeReducing X fun _ P => pure P
    let hF ← elabTermEnsuringType (← `(by $(⟨tac⟩))) (← mkAppM ``IOrder.IMono #[PROP, F])
    synthesizeSyntheticMVarsNoPostponing
    let hF ← instantiateMVars hF
    if hF.hasSorry then return
    -- `name.unfold`, quantified like `name`, and the names that law binders avoid.
    let avoid ← forallTelescopeReducing X fun ys _ => do
      let binders := (mkAppN fn ys).headBeta.getAppArgs.filter (·.isFVar)
      emitUnfold declName levels binders ys unfold fn pre
      binders.toList.mapM (·.fvarId!.getUserName)
    let emit (suffix : Name) (value : Expr) : MetaM Unit := do
      let type ← cleanup (← lawType avoid value)
      emitThm (declName ++ suffix) levels (← mkForallFVars fixed type) (← mkLambdaFVars fixed value)
    emitThm (declName ++ `pre_mono) levels
      (← mkForallFVars fixed (← unfoldOrders (← mkAppM ``IOrder.IMono #[PROP, pre])))
      (← mkLambdaFVars fixed hF)
    -- The generic laws, at `name.pre` and `name`.
    let law (lemma : Name) := mkAppM lemma #[isFix, hF]
    emit (if coind then `coiter else `iter) (← law ``IsFix.iter)
    emit `strong_mono (← law ``IsFix.strong_mono)
    emit (if coind then `coind else `ind) (← law ``IsFix.ind)
    emit (if coind then `paco else `ind_wf) (← law ``IsFix.ind_wf)
    let hm ← mkAppM ``IOrder.monotone_of_imono #[hF]
    -- `ne`, if an argument has an OFE.
    let ineType := mkApp2 (← mkConstWithFreshMVarLevels ``INe) X inst
    if let some ine ← observing? (synthInstance ineType) then
      if (ine.find? (·.isConstOf ``INe.instPiNE)).isSome then
        emit `ne (← mkAppM ``IsFix.ne #[isFix, hm])
    -- The instances: the generic theorems, with their hypotheses as instance arguments.
    let inst (suffix lemma : Name) (hyps : Nat) : MetaM Unit := do
      let value ← mkAppM lemma #[PROP, isFix, hm]
      let type ← cleanup (← lawType avoid value)
      let type ← forallBoundedTelescope type hyps fun hs b => do
        withNewBinderInfos (hs.map (·.fvarId!, .instImplicit)) (mkForallFVars hs b)
      emitThm (declName ++ suffix) levels (← mkForallFVars fixed type) (← mkLambdaFVars fixed value)
      addInstance (declName ++ suffix) .global (eval_prio default)
    if coind then
      inst `absorbing ``IsFix.gfp_absorbing 1
    else
      inst `affine ``IsFix.lfp_affine 1
      inst `absorbing ``IsFix.lfp_absorbing 1
      inst `persistent_affine ``IsFix.lfp_persistent_affine 2
      inst `persistent_absorbing ``IsFix.lfp_persistent_absorbing 2

/-- `ifix name binders : type := body`: the least fixpoint, by `partial_fixpoint`; `icofix`: the
greatest. The body is a term or match alternatives. -/
syntax (name := ifixCmd) declModifiers ("ifix " <|> "icofix ") declId Lean.Parser.Command.optDeclSig
  ((" := " term) <|> Lean.Parser.Term.matchAltsWhereDecls) (ppDedent(ppLine) monotoneClause)? :
  command

/-- `ifix`/`icofix`: the definition by `partial_fixpoint`, in the order of `MonotoneFixpoint`
(`CoMonotoneFixpoint`), and then, if it succeeded, its laws. -/
@[command_elab ifixCmd] meta def elabIfix : CommandElab := fun stx => do
  let #[mods, kw, id, sig, body, clause] := stx.getArgs | throwUnsupportedSyntax
  let coind := (kw.find? (·.getAtomVal.trimAscii == "icofix")).isSome
  let ord := if coind then `Iris.CoMonotoneFixpoint else `Iris.MonotoneFixpoint
  let mods : TSyntax ``Lean.Parser.Command.declModifiers := ⟨mods⟩
  let (id, sig) : TSyntax ``Lean.Parser.Command.declId × TSyntax ``Lean.Parser.Command.optDeclSig :=
    (⟨id⟩, ⟨sig⟩)
  -- The monotonicity tactic, on `IMono PROP F`.
  let tac ← match clause.getOptional? with
    | some c => `(tactic| (ifix_unfold; $(⟨c[1]⟩)))
    | none => `(tactic| ifix_monotone_default)
  let body : Term ← if body[0].isAtom then pure ⟨body[1]⟩ else `(fun $(⟨body[0]⟩):matchAlts)
  -- A non-recursive body refers to the definition, so that `partial_fixpoint` still defines it as
  -- a fixpoint; `emitLaws` removes the reference.
  let name : Ident := ⟨id.raw[0]⟩
  let full ← fullName name.getId
  let recursive := (body.raw.find? fun s => s.isIdent && s.getId.isSuffixOf full).isSome
  let body ← if recursive then pure body else `(let _ := $name; $body)
  unless (← getEnv).contains full do liftCoreM <| checkFresh full [`pre, `iter, `coiter]
  withScope (fun sc => { sc with opts := synthInstance.maxSize.set sc.opts 4096 }) do
  let defCmd (body : Term) := `(command| open scoped $(mkIdent ord) in
    $mods:declModifiers def $id $sig := $body
      partial_fixpoint monotonicity by ifix_monotone $tac:tactic)
  -- A body without BI operations does not include the `BI` instance of the section: if the
  -- definition fails, retry with a mention of the BI `bi%`.
  if let some errs ← tryElab (← defCmd body) then
    if (← tryElab (← defCmd (← `(let _ : Iris.BI bi% := inferInstance; $body)))).isSome then
      reportErrors errs
      return
  pushScope
  activateScoped ord
  try liftTermElabM do emitLaws (← resolveDeclared full) coind tac finally popScope

end Iris.Fixpoint
