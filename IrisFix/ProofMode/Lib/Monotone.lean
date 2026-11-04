/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public meta import IrisFix.BI.Lib.Monotone
public meta import IrisFix.BI.Lib.Fixpoint
public meta import Iris.ProofMode
public meta import Lean.Meta.Sym
public meta import Lean.LabelAttribute

namespace Iris

open Lean Elab Tactic Meta BI

open Sym in
/-- Decompose `goal` by `rules`, introducing quantifiers; returns the goals no rule applies to. -/
meta partial def decompose (rules : List BackwardRule) (goal : MVarId) : SymM (List MVarId) := do
  for rule in rules do
    if let .goals goals ← rule.apply goal then
      let goals' ← goals.mapM fun goal => do
        let .goal _ goal ← intros goal | decompose rules goal
        decompose rules goal
      return goals'.flatten
  return [goal]

/-- Show a goal `IMonoPred R P P'` as the BI statement `⊢ □ R -∗ P -∗ P'`, in an error. -/
meta def showIMonoPred (goal : MVarId) : MetaM MessageData := goal.withContext do
  let some target ← unfoldDefinition? (← instantiateMVars (← goal.getType))
    | return .ofGoal goal
  return .ofGoal (← mkFreshExprSyntheticOpaqueMVar target).mvarId!

/-- Unfold `IMono`, `all` and the pointwise operations at their instances, into the plain BI
statements that they stand for. The quantifiers that they introduce take the names of the
parameters of the domain, as explicit binders. -/
public meta def unfoldOrders (e : Expr) : MetaM Expr := do
  let e ← Meta.transform e
    (pre := fun e => do
      if e.isAppOf ``IOrder.IMono || e.isAppOf ``PointwiseLifting.all then
        if let some e ← unfoldDefinition? e then return .visit e.headBeta
      return .continue)
    (post := fun e => do
      let some n := e.getAppFn.constName? | return .continue
      unless n ∈ [``IOrder.le, ``IOrder.meet, ``INe.ne, ``Lean.Order.PartialOrder.rel,
        ``PointwiseLifting.rel, ``PointwiseLifting.map, ``PointwiseLifting.zip,
        ``IPointwiseLifting.irel] do return .continue
      let some e' ← unfoldProjInst? e | return .continue
      let e' := e'.headBeta
      -- On a function type, these bind its parameter: name the binder after the parameter, if it
      -- is named.
      let .forallE x .. ← whnfR (← inferType e.appArg!) | return .visit e'
      let name (y : Name) := if x.hasMacroScopes then y else x
      return .visit <| match e' with
        -- `ne` at an argument with an OFE binds two values: `x` and `x'`.
        | .forallE y t (.forallE y' t' b _) _ => .forallE (name y) t
          (.forallE (if n == ``INe.ne then (name y).appendAfter "'" else y') t' b .default) .default
        | .app f (.lam y t b _) => .app f (.lam (name y) t b .default)
        | .forallE y t b _ => .forallE (name y) t b .default
        | .lam y t b _ => .lam (name y) t b .default
        | e' => e')
  Core.betaReduce e

/-- Reduce a `match` on constructors. -/
meta def reduceMatch (e : Expr) : MetaM Expr := do
  let .reduced e ← reduceMatcher? e | return e
  return e.headBeta

/-- The size of the constructors in `e`, which a structurally recursive call decreases. -/
meta partial def ctorSize (e : Expr) : MetaM Nat := do
  if let some n ← evalNat e then return n
  if let some (_, k) ← isOffset? e then return k
  unless ← isConstructorApp e do return 0
  e.getAppArgs.foldlM (fun n a => return n + (← ctorSize a)) 1

/-- Solve an `IMonoPred R P P'` goal: decompose by the `@[imono]` rules, split `match` and `if`,
unfold other definitions, and close the rest with `R` or a hypothesis. A recursive definition is
unfolded again only while the constructors in its arguments shrink (`unfolded` maps it to their
size). -/
meta partial def imonoGoal (rules : List Sym.BackwardRule) (goal : MVarId)
    (unfolded : NameMap Nat := {}) : TacticM Unit := goal.withContext do
  -- The rules match syntactically and Sym needs `let`-free terms: unfold reducible definitions
  -- (`name.pre`), beta-reduce, and inline `let`s first.
  let target ← Sym.unfoldReducible (← instantiateMVars (← goal.getType))
  let target ← Core.transform target (pre := fun
    | .letE _ _ v b _ => return .visit (b.instantiate1 v)
    | e => return .continue e)
  let goal ← goal.replaceTargetDefEq (← Core.betaReduce target)
  let goals ← Sym.SymM.run do decompose rules (← Sym.preprocessMVar goal)
  for goal in goals do
    setGoals [goal]
    goal.withContext do
      let target ← instantiateMVars (← goal.getType)
      let_expr IMonoPred _ _ _ P P' := target
        | throwError "imono: unexpected goal{indentD goal}"
      let .const fn _ := P.cleanupAnnotations.getAppFn
        | try evalTactic (← `(tactic| first
            | assumption
            | ((repeat (apply IMonoPred.spec)); exact IMonoPred.call)))
          catch _ => throwError "imono: not monotone, or not covered by an @[imono] rule\n\
            {← showIMonoPred goal}"
      if (← getProjectionFnInfo? fn).isSome then throwError "imono: no rule for {fn}"
      if (← isMatcher fn) || fn == ``ite || fn == ``dite then
        -- A `match` on constructors (such as a list of recursive calls) reduces.
        let (Q, Q') := (← reduceMatch P, ← reduceMatch P')
        if Q != P || Q' != P' then
          let target := mkAppN target.getAppFn (target.getAppArgs.set! 3 Q |>.set! 4 Q')
          imonoGoal rules (← goal.replaceTargetDefEq target) unfolded
          return
        -- `split` splits the left side; the right side must follow, so its discriminants must
        -- not mention the recursive call.
        let err := m!"imono: cannot split this `match`/`if` on both sides: its discriminants \
          mention the recursive call\n{← showIMonoPred goal}"
        try evalTactic (← `(tactic| split)) catch _ => throwError err
        for goal in ← getGoals do goal.withContext do
          let_expr IMonoPred _ _ _ P P' := ← instantiateMVars (← goal.getType) | pure ()
          let P' := P'.cleanupAnnotations
          if P'.isAppOf fn && !P.cleanupAnnotations.isAppOf fn && (← reduceMatch P') == P' then
            throwError err
        for goal in ← getGoals do imonoGoal rules goal unfolded
        return
      if isRecCore (← getEnv) fn then
        throwError "imono: no rule for the recursor {fn}; add an @[imono] rule for it, such as \
          `IMonoPred.natRec`"
      let size ← P.getAppArgs.foldlM (fun n a => return n + (← ctorSize a)) 0
      if (unfolded.find? fn).any (size ≥ ·) then
        throwError "imono: no rule for {fn}, after unfolding it once"
      -- A fixpoint of `ifix` or `iguarded` unfolds by its `unfold` law, to its body.
      let unfoldLaw := fn ++ `unfold
      try
        if (← getEnv).contains unfoldLaw then
          evalTactic (← `(tactic|
            simp (config := { singlePass := true }) only [$(mkIdent unfoldLaw):ident]))
        else evalTactic (← `(tactic| unfold $(mkIdent fn):ident))
      catch _ => throwError "imono: no rule for {fn}"
      for goal in ← getGoals do
        let recursive := ((← instantiateMVars (← goal.getType)).find? (·.isConstOf fn)).isSome
        imonoGoal rules goal (if recursive then unfolded.insert fn size else unfolded)
  setGoals []

/-- Prove `BIMono F`, `IOrder.IMono PROP F`, or their unfolding
`∀ Φ Ψ, ⊢ □ (∀ x, Φ x -∗ Ψ x) -∗ ∀ x, F Φ x -∗ F Ψ x` with any number of arguments `x`. -/
elab "imono" : tactic => do
  try
    evalTactic (← `(tactic| (
      try unfold BIMono
      try unfold IOrder.IMono
      intro Φ Ψ
      repeat (apply IMonoPred.arg; intro)
      change IMonoPred _ _ _)))
  catch _ => throwError "imono: expected a monotonicity goal, `BIMono F` or \
    `∀ Φ Ψ, ⊢ □ (∀ x, Φ x -∗ Ψ x) -∗ ∀ x, F Φ x -∗ F Ψ x`"
  let rules ← (``IMonoPred.refl :: (← labelled `imono).toList).mapM (Sym.mkBackwardRuleFromDecl ·)
  -- Show the order of `IOrder` as the BI wands in errors (flipped for `CoMonotoneFixpoint`).
  let goal ← getMainGoal
  imonoGoal rules <| ← goal.withContext do
    goal.replaceTargetDefEq (← unfoldOrders (← instantiateMVars (← goal.getType)))

end Iris
