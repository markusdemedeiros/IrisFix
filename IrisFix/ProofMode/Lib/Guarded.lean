/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import IrisFix.BI.Lib.FixpointBanach
public import IrisFix.Algebra.Approx
public import IrisFix.ProofMode.Lib.Fixpoint

/-! # `iguarded`

`iguarded name binders : type := body contractive_by tac` defines the guarded fixpoint of
`name.pre := fun name binders => body`. `name.approx` is the fixpoint of `IApprox.lift name.pre` by
`partial_fixpoint`, on approximations, and `name` its point: `name.eq_fixpoint` shows that it is the
Banach fixpoint. Every parameter varies. The laws are the laws of `IPoints`, at `name.pre`. -/

public section

namespace Iris.Fixpoint
open Lean Elab Command Term Meta

syntax contractiveClause := "contractive_by " Lean.Parser.Tactic.tacticSeq

/-- `iguarded name binders : type := body contractive_by tac`: the guarded fixpoint. -/
syntax (name := iguardedCmd) declModifiers "iguarded " ident bracketedBinder*
  " : " term " := " term ppDedent(ppLine) contractiveClause : command

/-- Emit `name.unfold`, at every argument, and the laws of `IPoints`, from `name.unfold_fun`. -/
meta def emitGuardedLaws (declName : Name) : TermElabM Unit := do
  let info ← getConstInfo (declName ++ `unfold_fun)
  let levels := info.levelParams
  let value := Lean.mkConst info.name (levels.map mkLevelParam)
  forallTelescope info.type fun fixed eq => do
    let some (X, fn, .app pre _) := eq.eq? | throwError "iguarded: unexpected{indentExpr eq}"
    let hf := mkAppN value fixed
    let emit (suffix : Name) (type value : Expr) : MetaM Unit := do
      emitThm (declName ++ suffix) levels (← mkForallFVars fixed type) (← mkLambdaFVars fixed value)
    -- `name.unfold`, at every argument.
    forallTelescope X fun xs _ => do
      let value ← xs.foldlM (fun eq x => mkCongrFun eq x) hf
      let type ← mkEq (mkAppN fn xs) (mkAppN (mkApp pre fn) xs)
      emit `unfold (← mkForallFVars xs type) (← mkLambdaFVars xs value)
    -- The laws of `IPoints`, at the fixpoint `name`.
    let PROP ← forallTelescope X fun _ P => pure P
    for (suffix, lemma) in [(`persistent, ``IPoints.fixpoint_persistent),
        (`absorbing, ``IPoints.fixpoint_absorbing), (`affine, ``IPoints.fixpoint_affine),
        (`persistent_absorbing, ``IPoints.fixpoint_persistent_absorbing),
        (`persistent_affine, ``IPoints.fixpoint_persistent_affine)] do
      let law ← mkAppOptM lemma #[PROP, none, X, none, none, none, none, pre, none, fn, hf]
      emit suffix (← cleanup pre pre fn (← inferType law)) law

@[command_elab iguardedCmd] meta def elabIguarded : CommandElab
  | `(command| $mods:declModifiers iguarded $name $binders* : $ty := $body
      contractive_by $tac) => do
    let pre := mkIdentFrom name (name.getId ++ `pre)
    let approx := mkIdentFrom name (name.getId ++ `approx)
    let sig ← if binders.isEmpty then pure ty else `(∀ $binders*, $ty)
    let lam ← if binders.isEmpty then pure body else `(fun $(binders.map (⟨·.raw⟩))* => $body)
    elabCommand (← `(command| @[reducible] def $pre : $sig → $sig := fun ($name : $sig) => $lam))
    elabCommand (← `(command|
      instance : Iris.OFE.Contractive ($pre : $sig → $sig) where distLater_dist := by $tac))
    elabCommand (← `(command|
      noncomputable def $approx : Iris.IApprox.Dom $sig :=
        Iris.IApprox.lift ($pre : $sig → $sig) $approx
      partial_fixpoint monotonicity fun _ _ h => Iris.IApprox.lift_mono _ _ _ h))
    -- TODO: the modifiers `mods`; `noncomputable` is one of them.
    let _ := mods
    elabCommand (← `(command| noncomputable def $name : $sig := Iris.IApprox.get $approx))
    let eqFix := mkIdentFrom name (name.getId ++ `eq_fixpoint)
    let unfoldFun := mkIdentFrom name (name.getId ++ `unfold_fun)
    let eqn := mkIdentFrom name (approx.getId ++ `eq_1)
    elabCommand (← `(command|
      theorem $eqFix : $name = Iris.fixpoint ($pre : $sig → $sig) :=
        Iris.IApprox.lift_eq_fixpoint _ (Eq.symm $eqn)))
    elabCommand (← `(command|
      theorem $unfoldFun : $name = ($pre : $sig → $sig) $name :=
        Iris.IApprox.lift_fix_get _ (Eq.symm $eqn)))
    let declName ← resolveDeclared name
    liftTermElabM <| emitGuardedLaws declName
  | _ => throwUnsupportedSyntax

end Iris.Fixpoint
