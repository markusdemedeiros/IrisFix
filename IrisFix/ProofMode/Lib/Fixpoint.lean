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
laws are the generic laws of `IOrder`, at `name.pre`: their statements unfold the `IOrder`
instances, so they quantify over the varying parameters, curried. Laws are emitted only if the
definition succeeds. A non-recursive body is a fixpoint too; a body without BI operations needs
`local bi`. Generated declarations of a protected `name` are protected. -/

public section

namespace Iris.Fixpoint
open Lean Elab Command Term Meta BI

syntax monotoneClause := "monotone_by " Lean.Parser.Tactic.tacticSeq

/-- The default monotonicity tactic of `ifix` and `icofix`, on the goal `IOrder.IMono PROP F`. It is
`imono`; extend it with `macro_rules`. -/
syntax "ifix_monotone_default" : tactic
macro_rules | `(tactic| ifix_monotone_default) => `(tactic| imono)

/-- Remove metadata, such as `partial_fixpoint`'s marks on recursive calls. -/
meta def stripMData (e : Expr) : CoreM Expr :=
  Core.transform e (pre := fun e => return match e with
    | .mdata _ e => .visit e
    | _ => .continue)

/-- The statement of a law: `e`, with the functional `F` folded into `pre`, the orders unfolded,
`fix pre _` folded into `fn`, and default values and auto-params dropped. -/
meta def cleanup (F pre fn : Expr) (e : Expr) : MetaM Expr := do
  let e ← unfoldOrders <| (← stripMData e).replace fun e =>
    if e == F then some pre
    else if e.isAppOfArity ``optParam 2 || e.isAppOfArity ``autoParam 2 then some (e.getArg! 0)
    else none
  Core.betaReduce <| e.replace fun e =>
    if e.isAppOfArity ``Lean.Order.fix 4 && e.getArg! 2 == pre then fn else none

/-- Close `monotone F` by `IOrder.monotone_of_imono`, proving `IMono PROP F` with `tac`. `PROP` is
the codomain of the domain of `F`. With `unfold`, the goal is shown unfolded, in the BI. -/
syntax (name := ifixMonotone) "ifix_monotone " &"unfold"? Lean.Parser.Tactic.tacticSeq : tactic

@[tactic ifixMonotone] meta def evalIfixMonotone : Tactic.Tactic
  | `(tactic| ifix_monotone $[unfold%$u]? $tac) => Tactic.withMainContext do
    let goal ← Tactic.getMainGoal
    let_expr Lean.Order.monotone X _ _ _ F := ← whnfR (← goal.getType)
      | throwError "ifix_monotone: expected a goal `monotone F`"
    let PROP ← forallTelescopeReducing X fun _ P => pure P
    let err := m!"ifix_monotone: the order of{indentExpr X}\nis not the order of `IOrder`"
    let imono ← try mkAppM ``IOrder.IMono #[PROP, F] catch _ => throwError err
    let hF ← mkFreshExprSyntheticOpaqueMVar (← if u.isSome then unfoldOrders imono else pure imono)
    let proof ← mkAppM ``IOrder.monotone_of_imono #[hF]
    unless ← isDefEq (← inferType proof) (← goal.getType) do throwError err
    goal.assign proof
    Tactic.replaceMainGoal [hF.mvarId!]
    Tactic.evalTactic tac
  | _ => throwUnsupportedSyntax

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

/-- Emit `name.pre`, `name.pre_mono`, `name.unfold` and the laws of `name`, a `partial_fixpoint`
proved monotone by `ifix_monotone`. `coind` names the laws for the greatest fixpoint. -/
meta def emitLaws (declName : Name) (coind : Bool) : TermElabM Unit := do
  let info ← getConstInfoDefn declName
  -- The definition, or its monotonicity proof, failed: the errors are already reported.
  if info.value.hasSorry then return
  checkFresh declName <| [`pre, `pre_mono, `unfold, `unfold_mp, `unfold_mpr, `strong_mono, `ne] ++
    if coind then [`coiter, `coind, `paco, `absorbing]
    else [`iter, `ind, `ind_wf, `affine, `absorbing, `persistent_affine, `persistent_absorbing]
  let levels := info.levelParams
  lambdaTelescope info.value fun params body => do
    -- If a fixed parameter follows a varying one, `partial_fixpoint` moves the fixed parameters
    -- first, into an auxiliary `fun fixed => fix X inst F h`, applied to the varying ones.
    let body ← match body.getAppFn with
      | .const n us => if n == ``Lean.Order.fix then pure body else do
        let ci ← getConstInfo n
        let some v := ci.value? | pure body
        pure <| (v.instantiateLevelParams ci.levelParams us).beta body.getAppArgs
      | _ => pure body
    let_expr Lean.Order.fix X inst F h := body.getAppPrefix 4
      | throwError "ifix: `{declName}` is not a `partial_fixpoint`"
    -- The laws and `pre` quantify over `X`, with explicit binders.
    let X := X.replace fun | .forallE x t b _ => some (.forallE x t b .default) | _ => none
    let varying := body.getAppArgs.extract 4
    let fixed := params.filter (!varying.contains ·)
    let avoid ← params.toList.mapM (·.fvarId!.getUserName)
    -- `partial_fixpoint` marks the recursive calls, and abstracts the monotonicity proof into an
    -- auxiliary theorem.
    let F := (← stripMData F).replace fun
      | .lam x t b _ => some (.lam x t b .default)
      | _ => none
    let h' := match h.getAppFn, h.getAppFn.constName?.bind (← getEnv).find? with
      | .const _ us, some (.thmInfo t) =>
        (t.value.instantiateLevelParams t.levelParams us).beta h.getAppArgs
      | _, _ => h
    let_expr IOrder.monotone_of_imono PROP _ _ _ iord _ hF := h'
      | throwError "ifix: unexpected monotonicity proof{indentExpr h'}"
    let fn ← mkLambdaFVars varying (mkAppN (.const declName (levels.map mkLevelParam)) params)
    let pre ← emitPre declName levels fixed (elimDeadLets F)
    let emit (suffix : Name) (value : Expr) : MetaM Unit := do
      let type ← cleanup F pre fn (← lawType avoid value)
      emitThm (declName ++ suffix) levels (← mkForallFVars fixed type) (← mkLambdaFVars fixed value)
    emit `pre_mono hF
    forallTelescopeReducing (← instantiateForall X varying) fun ys _ => do
      emitUnfold declName levels (params ++ ys) (varying ++ ys) (← mkAppM ``Lean.Order.fix_eq #[h])
        fn pre
    -- The generic laws, at `name.pre`.
    let law (lemma : Name) := mkAppOptM lemma #[PROP, none, X, inst, iord, pre, hF]
    emit (if coind then `coiter else `iter) (← law ``IOrder.fix_iter)
    emit `strong_mono (← law ``IOrder.fix_strong_mono)
    let lawMeet (lemma : Name) := mkAppOptM lemma #[PROP, none, X, inst, iord, pre, none, hF]
    emit (if coind then `coind else `ind) (← lawMeet ``IOrder.fix_ind)
    emit (if coind then `paco else `ind_wf) (← lawMeet ``IOrder.fix_ind_wf)
    -- `ne`, if an argument has an OFE.
    let ineType := mkApp2 (← mkConstWithFreshMVarLevels ``INe) X inst
    if let some ine ← observing? (synthInstance ineType) then
      if (ine.find? (·.isConstOf ``INe.instPiNE)).isSome then
        emit `ne (← mkAppOptM ``fix_ne #[X, inst, ine, pre, pre, h, h])
    -- The instances: the generic theorems, with their hypotheses as instance arguments.
    let inst (suffix lemma : Name) (hyps : Nat) : MetaM Unit := do
      let value ← mkAppOptM lemma #[PROP, none, X, inst, none, none, pre, h]
      let type ← cleanup F pre fn (← lawType avoid value)
      let type ← forallBoundedTelescope type hyps fun hs b => do
        withNewBinderInfos (hs.map (·.fvarId!, .instImplicit)) (mkForallFVars hs b)
      emitThm (declName ++ suffix) levels (← mkForallFVars fixed type) (← mkLambdaFVars fixed value)
      addInstance (declName ++ suffix) .global (eval_prio default)
    if coind then
      inst `absorbing ``IOrder.gfp_absorbing 1
    else
      inst `affine ``IOrder.lfp_affine 1
      inst `absorbing ``IOrder.lfp_absorbing 1
      inst `persistent_affine ``IOrder.lfp_persistent_affine 2
      inst `persistent_absorbing ``IOrder.lfp_persistent_absorbing 2

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
  let tac ← match clause.getOptional? with
    | some c => `(tactic| ifix_monotone unfold $(⟨c[1]⟩))
    | none => `(tactic| ifix_monotone ifix_monotone_default)
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
    $mods:declModifiers def $id $sig := $body partial_fixpoint monotonicity by $tac:tactic)
  -- A body without BI operations does not include the `BI` instance of the section: if the
  -- definition fails, retry with a mention of the BI `bi%`.
  if let some errs ← tryElab (← defCmd body) then
    if (← tryElab (← defCmd (← `(let _ : Iris.BI bi% := inferInstance; $body)))).isSome then
      reportErrors errs
      return
  pushScope
  activateScoped ord
  try liftTermElabM do emitLaws (← resolveDeclared full) coind finally popScope

end Iris.Fixpoint
