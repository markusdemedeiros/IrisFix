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

`iguarded name binders : type := body contractive_by tac` defines the guarded fixpoint `name` of
`name.pre := fun name binders => body`, as the point of the least fixpoint of `Approx.lift name.pre`
on approximations of its type. `name.eq_fixpoint` shows that it is the Banach fixpoint. Every
parameter varies; section variables are fixed. The laws are the Banach laws, at `name.pre`. -/

public section

namespace Iris.Fixpoint
open Lean Elab Command Term Meta

syntax contractiveClause := "contractive_by " Lean.Parser.Tactic.tacticSeq

/-- The default contractiveness tactic of `iguarded`, on the goal `Contractive name.pre`; extend it
with `macro_rules`. -/
syntax "iguarded_contractive_default" : tactic
macro_rules
  | `(tactic| iguarded_contractive_default) =>
    `(tactic| fail "iguarded: prove that the body is contractive with `contractive_by`")

/-- `iguarded name binders : type := body contractive_by tac`: the guarded fixpoint. -/
syntax (name := iguardedCmd) declModifiers "iguarded " declId bracketedBinder*
  " : " term " := " term (ppDedent(ppLine) contractiveClause)? : command

/-- Make `name` irreducible, and emit `name.pre`, for `name := Approx.get (fix (lift pre) _)`.
Return `name.pre` at the parameters of `name`, as syntax: section variables and auto-bound
implicits, by name, and instances, by `_`. -/
meta def emitGuardedPre (declName : Name) : TermElabM Term := do
  let info ← getConstInfoDefn declName
  setReducibilityStatus declName .irreducible
  lambdaTelescope info.value fun fixed body => do
    let_expr Iris.Approx.get _ _ S := body | throwError "iguarded: unexpected{indentExpr body}"
    let_expr Lean.Order.fix _ _ L _ := S | throwError "iguarded: unexpected{indentExpr S}"
    let_expr Iris.Approx.lift _ _ _ G := L | throwError "iguarded: unexpected{indentExpr L}"
    discard <| emitPre declName info.levelParams fixed G
    let args ← fixed.mapM fun x => do
      let d ← x.fvarId!.getDecl
      if d.binderInfo.isInstImplicit || d.userName.hasMacroScopes then `(_)
      else pure (mkIdent d.userName)
    `(@$(mkCIdent (declName ++ `pre)) $args*)

/-- Emit `name.eq_fixpoint`, `name.unfold_fun`, `name.unfold`, at every argument, and the Banach
laws, from the instance `name.pre.contractive`. The laws take its parameters: those of `name`, and
the section variables its proof uses. -/
meta def emitGuardedLaws (declName : Name) (cName : Name) : TermElabM Unit := do
  let info ← getConstInfoDefn declName
  let cInfo ← getConstInfo cName
  let levels := cInfo.levelParams
  forallTelescope cInfo.type fun params cType => do
    let c := mkAppN (.const cName (levels.map mkLevelParam)) params
    let_expr OFE.Contractive _ _ _ _ pre := cType | throwError "iguarded: unexpected{indentExpr cType}"
    let .const _ us := pre.getAppFn | throwError "iguarded: unexpected{indentExpr pre}"
    let fixed := pre.getAppArgs
    let fn := mkAppN (.const declName us) fixed
    let body := (info.value.instantiateLevelParams info.levelParams us).beta fixed
    let_expr Iris.Approx.get X _ S := body | throwError "iguarded: unexpected{indentExpr body}"
    let_expr Lean.Order.fix _ _ L h := S | throwError "iguarded: unexpected{indentExpr S}"
    let_expr Iris.Approx.lift _ _ inh _ := L | throwError "iguarded: unexpected{indentExpr L}"
    let emit (suffix : Name) (type value : Expr) : MetaM Unit := do
      emitThm (declName ++ suffix) levels (← mkForallFVars params type)
        (← mkLambdaFVars params value)
    -- `name = name.pre name`, and `name` is the Banach fixpoint, for any default point.
    let hS ← mkEqSymm (← mkAppM ``Lean.Order.fix_eq #[h])
    emit `unfold_fun (← mkEq fn (mkApp pre fn))
      (← mkAppOptM ``Approx.lift_fix_get #[X, none, inh, pre, c, S, hS])
    withLocalDeclD `j (← mkAppM ``Inhabited #[X]) fun j =>
    withNewBinderInfos #[(j.fvarId!, .instImplicit)] do
      let fp ← mkAppOptM ``fixpoint #[X, none, j, pre, c]
      emit `eq_fixpoint (← mkForallFVars #[j] (← mkEq fn fp)) (← mkLambdaFVars #[j]
        (← mkAppOptM ``Approx.get_eq_fixpoint #[X, none, none, inh, j, pre, c, S, hS]))
    let hf := mkAppN (.const (declName ++ `unfold_fun) (levels.map mkLevelParam)) params
    -- `name.unfold`, at every argument.
    forallTelescopeReducing X fun xs P => do
      emitUnfold declName levels (params ++ xs) xs hf fn pre
      let P ← whnfR P
      let avoid ← xs.toList.mapM (·.fvarId!.getUserName)
      -- The Banach laws, at the fixpoint `name`, if its values are in a BI not depending on `xs`.
      if P.hasAnyFVar (xs.contains <| .fvar ·) then return
      for suffix in guardedLaws do
        let lemma := `Iris.Banach ++ .mkSimple ("fixpoint_" ++ suffix.toString)
        let some law ← observing? <|
          mkAppOptM lemma #[P, none, X, none, none, none, none, pre, c, fn, hf] | continue
        emit suffix (← cleanup pre pre fn (← lawType avoid law)) law
where guardedLaws := [`persistent, `absorbing, `affine, `persistent_absorbing, `persistent_affine,
    `plain, `plain_absorbing, `plain_affine]

@[command_elab iguardedCmd] meta def elabIguarded : CommandElab
  | `(command| $mods:declModifiers iguarded $id $binders* : $ty := $body $[$clause]?) => do
    let tac ← match clause with
      | some c => match c with
        | `(contractiveClause| contractive_by $tac) => `(by $tac)
        | _ => throwUnsupportedSyntax
      | none => `(by iguarded_contractive_default)
    for b in binders do
      if b.raw.getKind == ``Lean.Parser.Term.explicitBinder && !b.raw[3].isNone then
        throwErrorAt b "iguarded: parameters cannot have default values"
    -- `Approx.get` is noncomputable.
    let mods : TSyntax ``Lean.Parser.Command.declModifiers := ⟨if !mods.raw[4].isNone then mods.raw
      else mods.raw.setArg 4 (mkNullNode #[mkNode ``Lean.Parser.Command.noncomputable
        #[mkAtom "noncomputable "]])⟩
    let name : Ident := ⟨id.raw[0]⟩
    let full ← fullName name.getId
    let names := [`pre, `pre.contractive, `eq_fixpoint, `unfold_fun, `unfold, `unfold_mp,
      `unfold_mpr] ++ emitGuardedLaws.guardedLaws
    unless (← getEnv).contains full do liftCoreM <| checkFresh full names
    -- The recursive occurrences, written like the definition: a binder.
    let self := mkIdentFrom name (.mkSimple name.getId.getString!)
    let renamed ← body.raw.replaceM fun s =>
      pure <| if s.isIdent && s.getId == name.getId then some self else none
    let body : Term := if name.getId.isAtomic then body else ⟨renamed⟩
    let sig ← if binders.isEmpty then pure ty else `(∀ $binders*, $ty)
    let lam ← if binders.isEmpty then pure body else `(fun $(binders.map (⟨·.raw⟩))* => $body)
    if let some errs ← tryElab (← `(command|
        $mods:declModifiers def $id : $sig := no_implicit_lambda%
          (@Iris.Approx.get $sig _ (Lean.Order.fix (Iris.Approx.lift fun ($self : $sig) =>
            no_implicit_lambda% $lam) (Iris.Approx.lift_mono _))))) then
      reportErrors errs
      return
    let declName ← liftCoreM <| resolveDeclared full
    if (← getConstInfoDefn declName).value.hasSorry then return
    let pre ← runTermElabM fun _ => emitGuardedPre declName
    -- The `Contractive` instance, an ordinary declaration: it includes the section variables its
    -- proof uses.
    let instId : Ident := mkIdentFrom name (name.getId ++ `pre.contractive)
    let instMods : TSyntax ``Lean.Parser.Command.declModifiers :=
      ⟨(mods.raw.setArg 0 mkNullNode).setArg 1 mkNullNode⟩
    if let some errs ← tryElab (← `(command|
        $instMods:declModifiers instance $(⟨id.raw.setArg 0 instId⟩):declId :
          Iris.OFE.Contractive $pre := Iris.OFE.Contractive.mk $(⟨tac⟩))) then
      reportErrors errs
      return
    let cName ← liftCoreM <| resolveDeclared (full ++ `pre.contractive)
    runTermElabM fun _ => emitGuardedLaws declName cName
  | _ => throwUnsupportedSyntax

end Iris.Fixpoint
