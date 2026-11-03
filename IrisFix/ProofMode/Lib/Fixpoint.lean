/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import IrisFix.BI.Lib.Pointwise
public meta import IrisFix.ProofMode.Lib.Monotone

/-! # `ifix` and `icofix`

`ifix name binders : type := body` defines `name` by `partial_fixpoint`, in the order of
`MonotoneFixpoint` (`icofix`: `CoMonotoneFixpoint`), which also infers the fixed parameters. The
laws are the generic laws of `IOrder`, at `name.pre`: their statements unfold the `IOrder`
instances, so they quantify over the varying parameters, curried. -/

public section

namespace Iris.Fixpoint
open Lean Elab Command Term Meta BI

syntax monotoneClause := "monotone_by " Lean.Parser.Tactic.tacticSeq

/-- Close `monotone F` by `IOrder.monotone_of_imono`, proving `IMono PROP F` with `tac`. `PROP` is
the codomain of the domain of `F`. -/
syntax (name := ifixMonotone) "ifix_monotone " Lean.Parser.Tactic.tacticSeq : tactic

@[tactic ifixMonotone] meta def evalIfixMonotone : Tactic.Tactic
  | `(tactic| ifix_monotone $tac) => Tactic.withMainContext do
    let goal ← Tactic.getMainGoal
    let_expr Lean.Order.monotone X _ _ _ F := ← whnfR (← goal.getType)
      | throwError "ifix_monotone: expected a goal `monotone F`"
    let PROP ← forallTelescope X fun _ P => pure P
    let hF ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``IOrder.IMono #[PROP, F])
    let proof ← mkAppM ``IOrder.monotone_of_imono #[hF]
    unless ← isDefEq (← inferType proof) (← goal.getType) do
      throwError "ifix_monotone: the order of{indentExpr X}\nis not the order of `IOrder`"
    goal.assign proof
    Tactic.replaceMainGoal [hF.mvarId!]
    Tactic.evalTactic tac
  | _ => throwUnsupportedSyntax

/-- The full name of `name`, just declared in the current namespace. -/
meta def resolveDeclared (name : Ident) : CommandElabM Name := do
  let full := (← getCurrNamespace) ++ name.getId
  let env ← getEnv
  if env.contains full then return full
  let priv := mkPrivateName env full
  if env.contains priv then return priv
  throwErrorAt name "unknown declaration `{full}`"

/-- Remove metadata, such as `partial_fixpoint`'s marks on recursive calls. -/
meta def stripMData (e : Expr) : CoreM Expr :=
  Core.transform e (pre := fun e => return match e with
    | .mdata _ e => .visit e
    | _ => .continue)

/-- Unfold the `IOrder` operations and `IMono`, and fold the functional `F` into `pre` and
`fix pre _` into `fn`. The quantifiers of the unfolded orders take the names of the parameters of
the domain. -/
meta def cleanup (F pre fn : Expr) (e : Expr) : MetaM Expr := do
  let e ← stripMData e
  let e := e.replace fun e => if e == F then some pre else none
  let e ← Meta.transform e
    (pre := fun e => do
      if e.isAppOf ``IOrder.IMono then
        if let some e ← unfoldDefinition? e then return .visit e.headBeta
      return .continue)
    (post := fun e => do
      if e.isAppOfArity ``Lean.Order.fix 4 && e.getArg! 2 == pre then return .done fn
      let some n := e.getAppFn.constName? | return .continue
      unless n ∈ [``IOrder.le, ``IOrder.meet, ``IOrder.map, ``IOrder.ne, ``IPoints.all,
        ``Lean.Order.PartialOrder.rel] do return .continue
      let some e' ← unfoldProjInst? e | return .continue
      let e' := e'.headBeta
      -- On a function type, these bind its parameter: name the binder after the parameter.
      if let .forallE x .. ← whnfR (← inferType (e.getArg! (e.getAppNumArgs - 1))) then
        match e' with
        | .app f (.lam _ t b bi) => return .visit (.app f (.lam x t b bi))
        | .forallE _ t b bi => return .visit (.forallE x t b bi)
        | .lam _ t b bi => return .visit (.lam x t b bi)
        | _ => pure ()
      return .visit e')
  Core.betaReduce e

/-- Add a theorem; the kernel checks `value` against `type`. -/
meta def emitThm (name : Name) (levels : List Name) (type value : Expr) : MetaM Unit := do
  let type ← instantiateMVars type
  let value ← instantiateMVars value
  addDecl <| .thmDecl { name, levelParams := levels, type, value }

/-- Emit `name.pre`, `name.pre_mono`, `name.unfold` and the laws of `name`, a `partial_fixpoint`
proved monotone by `ifix_monotone`. `coind` names the laws for the greatest fixpoint. -/
meta def emitLaws (declName : Name) (coind : Bool) : TermElabM Unit := do
  let info ← getConstInfoDefn declName
  let levels := info.levelParams
  let us := levels.map mkLevelParam
  lambdaTelescope info.value fun fixed body => do
    let_expr Lean.Order.fix X inst F h := body
      | throwError "ifix: `{declName}` is not a `partial_fixpoint`"
    -- `partial_fixpoint` marks the recursive calls.
    let F ← stripMData F
    -- `partial_fixpoint` abstracts the monotonicity proof into an auxiliary theorem.
    let env ← getEnv
    let h' := match h.getAppFn with
      | .const n us => match env.find? n with
        | some (.thmInfo t) => (t.value.instantiateLevelParams t.levelParams us).beta h.getAppArgs
        | _ => h
      | _ => h
    let_expr IOrder.monotone_of_imono PROP _ _ _ _ _ iord _ hF := h'
      | throwError "ifix: unexpected monotonicity proof{indentExpr h'}"
    let fn := mkAppN (.const declName us) fixed
    -- `name.pre` and `name.pre_mono`.
    let preName := declName ++ `pre
    addDecl <| .defnDecl
      { name := preName, levelParams := levels, type := ← mkForallFVars fixed (← inferType F)
        value := ← mkLambdaFVars fixed F, hints := .abbrev, safety := .safe }
    setReducibilityStatus preName .reducible
    let pre := mkAppN (.const preName us) fixed
    let emit (suffix : Name) (value : Expr) : MetaM Unit := do
      let type ← cleanup F pre fn (← inferType value)
      emitThm (declName ++ suffix) levels (← mkForallFVars fixed type) (← mkLambdaFVars fixed value)
    emit `pre_mono hF
    -- `name.unfold`, at every varying argument.
    forallTelescope X fun xs _ => do
      let eq ← mkAppM ``Lean.Order.fix_eq #[h]
      let value ← xs.foldlM (fun eq x => mkCongrFun eq x) eq
      let type ← mkEq (mkAppN fn xs) (mkAppN (mkApp pre fn) xs)
      emitThm (declName ++ `unfold) levels (← mkForallFVars (fixed ++ xs) type)
        (← mkLambdaFVars (fixed ++ xs) value)
    -- The generic laws, at `name.pre`.
    let law (lemma : Name) := mkAppOptM lemma #[PROP, none, none, X, inst, none, iord, pre, hF]
    emit (if coind then `coiter else `iter) (← law ``IOrder.fix_iter)
    emit `strong_mono (← law ``IOrder.fix_strong_mono)
    emit (if coind then `coind else `ind) (← law ``IOrder.fix_ind)
    emit (if coind then `paco else `ind_wf) (← law ``IOrder.fix_ind_wf)
    -- `ne`, if an argument has an OFE.
    if (iord.find? (·.isConstOf ``IOrder.instPiNE)).isSome then
      emit `ne (← mkAppOptM ``IOrder.fix_ne #[PROP, none, none, X, inst, none, iord, pre, h])
    -- The instances: the generic theorems, with their hypotheses as instance arguments.
    let inst (suffix lemma : Name) (hyps : Nat) : MetaM Unit := do
      let value ← mkAppOptM lemma #[PROP, none, X, inst, none, iord, pre, h]
      let type ← cleanup F pre fn (← inferType value)
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

syntax (name := ifixLaws) "ifix_laws " ident (&"coind")? : command

@[command_elab ifixLaws] meta def elabIfixLaws : CommandElab
  | `(command| ifix_laws $name $[coind%$c]?) => do
    let declName ← resolveDeclared name
    liftTermElabM <| emitLaws declName c.isSome
  | _ => throwUnsupportedSyntax

/-- `ifix name binders : type := body`: the least fixpoint, by `partial_fixpoint`. -/
syntax (name := ifixCmd) declModifiers "ifix " declId Lean.Parser.Command.optDeclSig " := " term
  (ppDedent(ppLine) monotoneClause)? : command

/-- `icofix name binders : type := body`: the greatest fixpoint, by `partial_fixpoint`. -/
syntax (name := icofixCmd) declModifiers "icofix " declId Lean.Parser.Command.optDeclSig " := " term
  (ppDedent(ppLine) monotoneClause)? : command

/-- The commands for `ifix`/`icofix`, in the order of `ord`. -/
meta def expand (mods : TSyntax ``Lean.Parser.Command.declModifiers)
    (id : TSyntax ``Lean.Parser.Command.declId) (sig : TSyntax ``Lean.Parser.Command.optDeclSig)
    (body : Term) (clause : Option (TSyntax ``monotoneClause)) (ord : Ident) (coind : Bool) :
    MacroM (TSyntax `command) := do
  let tac ← match clause with
    | some c => match c with
      | `(monotoneClause| monotone_by $tac) => pure tac
      | _ => Macro.throwUnsupported
    | none => `(Lean.Parser.Tactic.tacticSeq| imono)
  let name : Ident := ⟨id.raw[0]⟩
  let laws ← if coind then `(command| ifix_laws $name coind) else `(command| ifix_laws $name)
  `(open scoped $ord in
    $mods:declModifiers def $id $sig := $body
    partial_fixpoint monotonicity by ifix_monotone $tac
    open scoped $ord in
    $laws:command)

macro_rules
  | `(command| $mods:declModifiers ifix $id $sig := $body $[$clause]?) =>
    expand mods id sig body clause (mkIdent `Iris.MonotoneFixpoint) false
  | `(command| $mods:declModifiers icofix $id $sig := $body $[$clause]?) =>
    expand mods id sig body clause (mkIdent `Iris.CoMonotoneFixpoint) true

end Iris.Fixpoint
