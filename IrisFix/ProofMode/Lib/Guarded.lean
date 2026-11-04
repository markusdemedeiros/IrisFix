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

`iguarded name binders : type := body contractive_by tac` defines the guarded fixpoint
`name.approx := bind₂ name.approx name.pre` by `partial_fixpoint`, on approximations (balls) of
`type`, and `name := get ∘ name.approx`. `tac` proves `name.pre` contractive; then `name` unfolds
to `name.pre name` (`bind₂_get_approx`), and `name.eq_fixpoint` shows that it is the Banach
fixpoint. The laws are the Banach laws, at `name.pre`. Every parameter varies; section variables
are fixed. -/

public section

namespace Iris.Fixpoint
open Lean Elab Command Term Meta Iris.Meta

syntax contractiveClause := "contractive_by " Lean.Parser.Tactic.tacticSeq

/-- The default contractiveness tactic of `iguarded`, on the goal `Contractive name.pre`; extend it
with `macro_rules`. -/
syntax "iguarded_contractive_default" : tactic
macro_rules
  | `(tactic| iguarded_contractive_default) =>
    `(tactic| fail "iguarded: prove that the body is contractive with `contractive_by`")

/-- `iguarded name binders : type := body contractive_by tac`: the guarded fixpoint. The body is a
term or match alternatives. -/
syntax (name := iguardedCmd) declModifiers "iguarded " fixDecl
  (ppDedent(ppLine) contractiveClause)? : command

/-- Emit `name.pre`, `name.pre.contractive`, `name.unfold_fun`, `name.eq_fixpoint`, `name.unfold`,
at every argument, and the Banach laws, for `name := get ∘ name.approx`. `tac` proves `name.pre`
contractive, with the section variables `vars`; the laws take those that its proof uses. -/
meta def emitGuardedLaws (declName approxName : Name) (tac : Syntax) (vars : Array Expr) :
    TermElabM Unit := do
  let info ← getConstInfoDefn approxName
  if info.value.hasSorry then return
  let laws := [`persistent, `absorbing, `affine, `persistent_absorbing, `persistent_affine, `plain,
    `plain_absorbing, `plain_affine]
  checkFresh declName <| [`pre, `pre.contractive, `eq_fixpoint, `unfold_fun, `unfold, `unfold_mp,
    `unfold_mpr] ++ laws
  setReducibilityStatus declName .irreducible
  let levels := info.levelParams
  let us := levels.map mkLevelParam
  readFix approxName us vars fun { fixed, fn, body, isFix, .. } => do
    -- `name`, and its type `X`.
    let fn := fn.replace fun e => if e.isConstOf approxName then some (.const declName us) else none
    let X := (← inferType body).bindingDomain!
    let pre ← emitPre declName levels fixed body
    let cType ← mkAppM ``OFE.Contractive #[pre]
    let some c ← proveBy tac cType ``OFE.Contractive.mk | return
    let params := lawParams fixed vars c
    -- The laws, with `cv`, a local instance standing for `c`.
    withLocalDecl `c .instImplicit cType fun cv => do
    let emit (suffix : Name) (type value : Expr) : MetaM Unit := do
      emitThm (declName ++ suffix) levels (← mkForallFVars params (type.replaceFVar cv c))
        (← mkLambdaFVars params (value.replaceFVar cv c))
    emit `pre.contractive cType cv
    -- An instance, unless `name.pre` unfolds to a body without some parameter: instance search
    -- would then match it against unrelated goals, such as `Contractive later`.
    if ← fixed.allM fun x => do
        return (← x.fvarId!.getBinderInfo).isInstImplicit || body.containsFVar x.fvarId! then
      addInstance (declName ++ `pre.contractive) .global (eval_prio default)
    -- `name = name.pre name`, and `name` is the Banach fixpoint, for any default point.
    emit `unfold_fun (← mkEq fn (mkApp pre fn)) (← mkAppM ``Approx.IsFix.get_approx #[cv, isFix])
    let hf := mkAppN (.const (declName ++ `unfold_fun) us) params
    withLocalDecl `j .instImplicit (← mkAppM ``Inhabited #[X]) fun j => do
      emit `eq_fixpoint (← mkForallFVars #[j] (← mkEq fn (mkApp (← mkAppM ``fixpoint #[pre]) cv)))
        (← mkLambdaFVars #[j] (← mkAppM ``Approx.eq_fixpoint #[pre, hf]))
    -- `name.unfold`, at every argument.
    forallTelescopeReducing X fun xs P => do
      emitUnfold declName levels (params ++ xs) xs hf fn pre
      let P ← whnfR P
      let avoid ← xs.toList.mapM (·.fvarId!.getUserName)
      -- The Banach laws, at the fixpoint `name`, if its values are in a BI not depending on `xs`.
      if P.hasAnyFVar (xs.contains <| .fvar ·) then return
      for suffix in laws do
        let lemma := `Iris.Banach ++ .mkSimple ("fixpoint_" ++ suffix.toString)
        let some law ← observing? (mkAppM lemma #[P, pre, hf]) | continue
        emit suffix (← cleanup (← lawType avoid law)) law

@[command_elab iguardedCmd] meta def elabIguarded : CommandElab := fun stx => do
  let #[mods, _, decl, clause] := stx.getArgs | throwUnsupportedSyntax
  let d ← FixDecl.read "iguarded" decl
  let tac ← match clause.getOptional? with
    | some c => `(tactic| ($(⟨c[1]⟩)))
    | none => `(tactic| iguarded_contractive_default)
  -- `Approx.get` is noncomputable.
  let mods ← addNoncomputableMod ⟨mods⟩
  unless (← getEnv).contains d.full do liftCoreM <| checkFresh d.full [`approx, `pre]
  let approxId : TSyntax ``Lean.Parser.Command.declId :=
    ⟨d.id.raw.setArg 0 (mkIdentFrom d.name (d.name.getId ++ `approx))⟩
  let approxType ← forallStx d.binders (← `(Iris.Approx $d.ty))
  withLargeInstances do
  unless ← elabDef (← `(command|
      $(auxMods mods):declModifiers def $approxId $d.paramBinders* : $approxType := $(← d.value)
      partial_fixpoint monotonicity $(mkCIdent ``Approx.bind₂_mono_approx))) do return
  let approxName ← liftCoreM <| resolveDeclared (d.full ++ `approx)
  unless ← elabDef (← `(command|
      $mods:declModifiers def $d.id $((d.params ++ d.binders).map (⟨·⟩))* : $d.ty :=
        Iris.Approx.get $(← applyByName approxName))) do return
  let declName ← liftCoreM <| resolveDeclared d.full
  runTermElabM (emitGuardedLaws declName approxName tac)

end Iris.Fixpoint
