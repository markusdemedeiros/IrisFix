/-
Stress tests: bodies of `ifix`/`icofix` and the default `imono` monotonicity tactic.
-/
module

public import Iris.BI
public import IrisFix.ProofMode.Lib.Fixpoint

@[expose] public section
open Iris BI

namespace IrisTest.Stress.Bodies

local bi PROP

variable {PROP : Type _} [BI PROP]

/-! ## Connectives around the recursive call (all accepted by `imono`) -/

ifix c_sep (n : Nat) : PROP := iprop% c_sep (n+1) ∗ c_sep n
ifix c_and (n : Nat) : PROP := iprop% c_and (n+1) ∧ c_and n
ifix c_or (n : Nat) : PROP := iprop% c_or (n+1) ∨ emp
ifix c_wandR (P : PROP) (n : Nat) : PROP := iprop% P -∗ c_wandR P (n+1)
ifix c_pureWand (n : Nat) : PROP := iprop% ⌜n = 0⌝ -∗ c_pureWand (n+1)
ifix c_persImp (n : Nat) : PROP := iprop% <pers> ⌜n = 0⌝ → c_persImp (n+1)
ifix c_forall (n : Nat) : PROP := iprop% ∀ m, c_forall (n+m)
ifix c_exists (n : Nat) : PROP := iprop% ∃ m, ⌜m < n⌝ ∗ c_exists m
ifix c_later (n : Nat) : PROP := iprop% ▷ c_later (n+1)
ifix c_laterN (n : Nat) : PROP := iprop% ▷^[n] c_laterN (n+1)
ifix c_laterIf (b : Bool) : PROP := iprop% ▷?b c_laterIf (!b)
ifix c_box (n : Nat) : PROP := iprop% □ c_box (n+1)
ifix c_boxIf (b : Bool) : PROP := iprop% □?b c_boxIf (!b)
ifix c_pers (n : Nat) : PROP := iprop% <pers> c_pers (n+1)
ifix c_persIf (b : Bool) : PROP := iprop% <pers>?b c_persIf (!b)
ifix c_aff (n : Nat) : PROP := iprop% <affine> c_aff (n+1)
ifix c_affIf (b : Bool) : PROP := iprop% <affine>?b c_affIf (!b)
ifix c_abs (n : Nat) : PROP := iprop% <absorb> c_abs (n+1)
ifix c_absIf (b : Bool) : PROP := iprop% <absorb>?b c_absIf (!b)
ifix c_ex0 (n : Nat) : PROP := iprop% ◇ c_ex0 (n+1)
ifix c_pure (n : Nat) : PROP := iprop% ⌜n = 3⌝ ∗ c_pure (n+1) ∧ ⌜True⌝
ifix c_overP (n : Nat) : PROP := iprop% ∀ (P : PROP), P -∗ ▷ c_overP n ∗ P
ifix c_deep (_n : Nat) : PROP := iprop% ▷ (c_deep 1 ∗ (c_deep 2 ∨ (c_deep 3 ∧ (∃ k, c_deep k ∗
  (∀ j, ⌜j < k⌝ -∗ c_deep j ∗ □ c_deep (j+1) ∗ <pers> c_deep j ∗ <affine> c_deep 0 ∗
    <absorb> ◇ c_deep 1)))))
ifix c_two (n m : Nat) : PROP := iprop% ∀ k, ∃ j, c_two (n+k) (m+j) ∗ ▷ c_two m n
ifix c_depFin (n : Nat) (v : Fin (n+1)) : PROP := iprop% ▷ c_depFin (n+1) v.succ ∨ c_depFin n 0
ifix c_pairArg (p : Nat × Nat) : PROP := let (a, b) := p; iprop(▷ c_pairArg (b, a))
ifix c_funArg (f : Nat → Nat) : PROP := iprop% ▷ c_funArg (f ∘ f)
ifix c_propBinder (n : Nat) : PROP := iprop% ∀ (_ : n > 0), ▷ c_propBinder (n - 1)
ifix c_exProp (n : Nat) : PROP := iprop% ∃ (_ : n = 0), c_exProp n
ifix c_forallFun (n : Nat) : PROP := iprop% ∀ (f : Nat → Nat), c_forallFun (f n)

section upd
variable [BIUpdate PROP]
ifix u_bupd (n : Nat) : PROP := iprop% |==> u_bupd (n+1)
ifix u_bupdW (P : PROP) (n : Nat) : PROP := iprop% P ==∗ u_bupdW P (n+1)
end upd

section fupd
variable [BIFUpdate PROP]
ifix u_fupd (E : CoPset) (n : Nat) : PROP := iprop% |={E}=> u_fupd E (n+1)
ifix u_fupd2 (E1 E2 : CoPset) (n : Nat) : PROP := iprop% |={E1,E2}=> u_fupd2 E1 E2 (n+1)
ifix u_stepfupd (E : CoPset) (n : Nat) : PROP := iprop% |={E}▷=> u_stepfupd E (n+1)
ifix u_stepfupd2 (E1 E2 : CoPset) (n : Nat) : PROP := iprop% |={E1}[E2]▷=> u_stepfupd2 E1 E2 (n+1)
ifix u_stepfupdN (E : CoPset) (k n : Nat) : PROP := iprop% |={E}▷=>^[k] u_stepfupdN E k (n+1)
ifix u_fupdW (E : CoPset) (P : PROP) (n : Nat) : PROP := iprop% P ={E}=∗ u_fupdW E P (n+1)
end fupd

/-! ## Big operators -/

ifix b_sepL (l : List Nat) : PROP := iprop% [∗list] x ∈ l, b_sepL [x]
ifix b_sepLk (l : List Nat) : PROP := iprop% [∗list] k ↦ x ∈ l, b_sepLk [x+k]
ifix b_andL (l : List Nat) : PROP := iprop% [∧list] x ∈ l, b_andL [x]
ifix b_orL (l : List Nat) : PROP := iprop% [∨list] x ∈ l, b_orL [x]
ifix b_sepL2 (l : List Nat) : PROP := iprop% [∗list] x;y ∈ l;l, b_sepL2 [x,y]
ifix b_pairs (l : List (Nat × Nat)) : PROP := iprop% [∗list] k ↦ p ∈ l, ▷ b_pairs [(p.2, k)]
ifix b_partial (l : List Nat) : PROP := iprop% [∗list] x ∈ l, b_partial (x :: l)
ifix b_eta (l : List Nat) : PROP := bigSepL (fun _ => b_eta ∘ List.singleton) l
ifix b_matchLam (l : List Nat) : PROP :=
  iprop([∗list] x ∈ l, match x with | 0 => emp | k+1 => b_matchLam [k])

/-! ## Control flow, `let`, helpers -/

ifix m_ite (n : Nat) : PROP := if n = 0 then iprop(emp) else iprop(▷ m_ite (n - 1))
ifix m_dite (n : Nat) : PROP := if h : n = 0 then iprop(⌜h = h⌝) else iprop(▷ m_dite (n - 1))
ifix m_match (n : Nat) : PROP := match n with
  | 0 => iprop(emp)
  | k+1 => iprop(▷ m_match k ∗ m_match k)
ifix m_match2 (n : Nat) (o : Option Nat) : PROP := match n, o with
  | 0, _ => iprop(emp)
  | k+1, none => iprop(▷ m_match2 k (some k))
  | k+1, some j => iprop(m_match2 k none ∨ m_match2 j none)
ifix m_depMatch (n : Nat) : PROP := match h : n with
  | 0 => iprop(⌜h = h⌝)
  | k+1 => iprop(▷ m_depMatch k)
ifix m_mod (n : Nat) : PROP := match n % 3 with
  | 0 => iprop(emp)
  | 1 => m_mod (n+1)
  | _ => iprop(▷ m_mod (n+2))
ifix m_nested (n : Nat) : PROP := iprop% emp ∗ (match n with | 0 => iprop(True) | k+1 => m_nested k)
  ∗ ▷ (if n < 3 then m_nested (n+1) else emp)
ifix m_twoMatches (n : Nat) : PROP := iprop% (match n with | 0 => emp | k+1 => m_twoMatches k) ∗
  (match n with | 0 => emp | k+1 => m_twoMatches k)
ifix m_binderIte (n : Nat) : PROP := iprop% ∀ m, if m < n then m_binderIte m else emp
ifix m_let (n : Nat) : PROP := let r := m_let (n+1); iprop(r ∗ r)
ifix m_letFn (n : Nat) : PROP := let next := m_letFn; iprop(next (n+1) ∗ next n)
ifix m_optElim (o : Option Nat) : PROP := o.elim iprop(emp) (fun n => iprop(▷ m_optElim (some (n+1))))
ifix m_cond (b : Bool) : PROP := cond b (m_cond false) iprop(emp)
ifix m_comp (n : Nat) : PROP := iprop% ▷ (m_comp ∘ Nat.succ) n
ifix m_id (n : Nat) : PROP := iprop% ▷ id (m_id (n+1))
open Classical in
noncomputable ifix m_classIte (p : Prop) (n : Nat) : PROP :=
  if p then m_classIte p (n+1) else iprop(emp)

def helper (g : Nat → PROP) (n : Nat) : PROP := iprop% g (n+1) ∗ ▷ g n
ifix h_helper (n : Nat) : PROP := helper h_helper n
ifix h_helperEta (n : Nat) : PROP := helper (fun m => h_helperEta m) n
def helper2 (P : PROP) : PROP := iprop% □ P ∗ P
ifix h_helper2 (n : Nat) : PROP := helper2 (h_helper2 (n+1))

-- A recursive helper needs an `@[imono]` rule; with one, `imono` uses it.
def allBelow (g : Nat → PROP) : Nat → PROP
  | 0 => iprop(emp)
  | n+1 => iprop(g n ∗ allBelow g n)

-- Limitation (by design): a recursive helper is unfolded again only while the constructors in its
-- arguments shrink; `allBelow h n` needs induction on `n`, so it needs an `@[imono]` rule.
/-- error: imono: no rule for IrisTest.Stress.Bodies.allBelow, after unfolding it once -/
#guard_msgs in
ifix h_rec (n : Nat) : PROP := iprop% allBelow h_rec n

@[imono] theorem allBelow_mono {R : PROP} {g g' : Nat → PROP}
    (h : ∀ k, IMonoPred R (g k) (g' k)) : ∀ {n}, IMonoPred R (allBelow g n) (allBelow g' n)
  | 0 => IMonoPred.refl
  | _+1 => IMonoPred.sep (h _) (allBelow_mono h)
ifix h_viaRule (n : Nat) : PROP := iprop% ▷ allBelow h_viaRule n

/-! ## Performance -/

ifix p_big (n : Nat) : PROP := iprop% 
  (p_big 0 ∗ p_big 1 ∗ p_big 2 ∗ p_big 3 ∗ p_big 4 ∗ p_big 5 ∗ p_big 6 ∗ p_big 7 ∗ p_big 8) ∧
  (p_big 0 ∨ p_big 1 ∨ p_big 2 ∨ p_big 3 ∨ p_big 4 ∨ p_big 5 ∨ p_big 6 ∨ p_big 7 ∨ p_big 8) ∧
  (▷ ▷ ▷ ▷ ▷ ▷ ▷ ▷ □ □ <pers> <affine> p_big n) ∧
  (∀ a b c d e, ∃ f g h, p_big (a+b+c+d+e+f+g+h))
ifix p_bigMatch (n : Nat) : PROP := match n with
  | 0 => iprop(emp) | 1 => p_bigMatch 0 | 2 => p_bigMatch 1 | 3 => p_bigMatch 2
  | 4 => p_bigMatch 3 | 5 => p_bigMatch 4 | 6 => p_bigMatch 5 | 7 => p_bigMatch 6
  | k+8 => iprop(▷ p_bigMatch k ∗
      (if k = 0 then p_bigMatch 3 else match k with | 0 => iprop(True) | j+1 => p_bigMatch j))

/-! ## Non-monotone bodies: rejected

A recursive call in a negative position (left of `-∗`/`→`, either side of `∗-∗`/`↔`) or under `⌜⌝`
is not monotone; `imono` stops at the first such call and shows the goal it cannot prove. -/

/--
error: imono: not monotone, or not covered by an @[imono] rule
PROP : Type u_1
inst✝ : BI PROP
Φ✝ Ψ✝ : Nat → PROP
x✝ : Nat
⊢ ⊢ (□ ∀ n, Φ✝ n -∗ Ψ✝ n) -∗ Ψ✝ (x✝ + 1) -∗ Φ✝ (x✝ + 1)
-/
#guard_msgs in
ifix n_wandL (n : Nat) : PROP := iprop% n_wandL (n+1) -∗ emp

/--
error: imono: not monotone, or not covered by an @[imono] rule
PROP : Type u_1
inst✝ : BI PROP
Φ✝ Ψ✝ : Nat → PROP
x✝ : Nat
⊢ ⊢ (□ ∀ n, Φ✝ n -∗ Ψ✝ n) -∗ Ψ✝ (x✝ + 1) -∗ Φ✝ (x✝ + 1)
-/
#guard_msgs in
ifix n_persImpL (n : Nat) : PROP := iprop% <pers> n_persImpL (n+1) → emp

/--
error: imono: not monotone, or not covered by an @[imono] rule
PROP : Type u_1
inst✝ : BI PROP
Φ✝ Ψ✝ : Nat → PROP
x✝ : Nat
⊢ ⊢ (□ ∀ n, Φ✝ n -∗ Ψ✝ n) -∗ Ψ✝ (x✝ + 1) -∗ Φ✝ (x✝ + 1)
-/
#guard_msgs in
ifix n_wandIff (n : Nat) : PROP := iprop% n_wandIff (n+1) ∗-∗ emp

/--
error: imono: not monotone, or not covered by an @[imono] rule
PROP : Type u_1
inst✝ : BI PROP
Φ✝ Ψ✝ : Nat → PROP
x✝ : Nat
⊢ ⊢ (□ ∀ n, Φ✝ n -∗ Ψ✝ n) -∗ Ψ✝ x✝ -∗ Φ✝ x✝
-/
#guard_msgs in
ifix n_both (n : Nat) : PROP := iprop% □ (n_both n -∗ n_both (n+1))

/-- error: imono: no rule for Iris.BI.BIBase.pure -/
#guard_msgs in
ifix n_pureRec (n : Nat) : PROP := iprop% ⌜n_pureRec (n+1) = emp⌝

/--
error: imono: not monotone, or not covered by an @[imono] rule
PROP : Type u_1
inst✝ : BI PROP
Φ✝ Ψ✝ : Nat → PROP
x✝ : Nat
⊢ ⊢ (□ ∀ n, Φ✝ n -∗ Ψ✝ n) -∗ Ψ✝ (x✝ + 1) -∗ Φ✝ (x✝ + 1)
-/
#guard_msgs in
ifix n_iff (n : Nat) : PROP := iprop% n_iff (n+1) ↔ emp

-- For `icofix` the order is flipped: the assumption is `Ψ n -∗ Φ n`.
/--
error: imono: not monotone, or not covered by an @[imono] rule
PROP : Type u_1
inst✝ : BI PROP
Φ✝ Ψ✝ : Nat → PROP
x✝ : Nat
⊢ ⊢ (□ ∀ n, Ψ✝ n -∗ Φ✝ n) -∗ Φ✝ (x✝ + 1) -∗ Ψ✝ (x✝ + 1)
-/
#guard_msgs in
icofix n_coWandL (n : Nat) : PROP := iprop% n_coWandL (n+1) -∗ emp

/-! ## `monotone_by` -/

ifix mb_imono (n : Nat) : PROP := iprop% ▷ mb_imono (n+1)
  monotone_by imono

-- The goal is the plain BI statement `∀ Φ Ψ, ⊢ □ (∀ n, Φ n -∗ Ψ n) -∗ ∀ n, F Φ n -∗ F Ψ n`
-- (`Ψ -∗ Φ` and `F Ψ -∗ F Φ` for `icofix`).
ifix mb_manual (n : Nat) : PROP := iprop% ▷ mb_manual (n+1)
  monotone_by intro Φ Ψ; iintro #H %n HP; iintro !>; iapply H $$ HP
icofix mb_manualCo (n : Nat) : PROP := iprop% ▷ mb_manualCo (n+1)
  monotone_by intro Φ Ψ; iintro #H %n HP; iintro !>; iapply H $$ HP
example (n : Nat) : mb_manual (PROP := PROP) n = iprop(▷ mb_manual (n+1)) := mb_manual.unfold n

-- A tactic that leaves the goal open, or fails, gives one error at that goal.
/--
error: unsolved goals
PROP : Type u_1
inst✝ : BI PROP
⊢ ∀ (Φ Ψ : Nat → PROP), ⊢ (□ ∀ n, Φ n -∗ Ψ n) -∗ ∀ n, ▷ Φ (n + 1) -∗ ▷ Ψ (n + 1)
-/
#guard_msgs in
ifix mb_skip (n : Nat) : PROP := iprop% ▷ mb_skip (n+1)
  monotone_by skip

/--
error: custom
PROP : Type u_1
inst✝ : BI PROP
⊢ ∀ (Φ Ψ : Nat → PROP), ⊢ (□ ∀ n, Φ n -∗ Ψ n) -∗ ∀ n, ▷ Φ (n + 1) -∗ ▷ Ψ (n + 1)
-/
#guard_msgs in
ifix mb_fail (n : Nat) : PROP := iprop% ▷ mb_fail (n+1)
  monotone_by fail "custom"

/-! ## `icofix` -/

icofix co_sep (n : Nat) : PROP := iprop% co_sep (n+1) ∗ ▷ co_sep n
icofix co_match (n : Nat) : PROP := match n with
  | 0 => iprop(emp)
  | k+1 => iprop(▷ co_match k ∨ co_match (k+2))
icofix co_big (l : List Nat) : PROP := iprop% [∗list] x ∈ l, co_big [x+1]
icofix co_forallEx (n : Nat) : PROP := iprop% ∀ m, ∃ k, ⌜k > m⌝ ∗ □ co_forallEx (n + k)
icofix co_helper (n : Nat) : PROP := helper co_helper n
icofix co_let (n : Nat) : PROP := let r := co_let (n+1); iprop(<pers> r ∧ ▷ r)
icofix co_viaRule (n : Nat) : PROP := iprop% ▷ allBelow co_viaRule n

/-! ## Helpers -/

def headOr (l : List PROP) : PROP := match l with | [] => iprop(emp) | P :: _ => P
ifix allL (Φ : Nat → PROP) (l : List Nat) : PROP := match l with
  | [] => iprop(emp)
  | x :: l => iprop(Φ x ∗ allL Φ l)
@[irreducible] def opaqueHelper (P : PROP) : PROP := iprop% ▷ P

/-! ## Formerly failing monotone bodies -/

-- `P → rec`: the premise of `→` flips, like that of `-∗`.
ifix f_impR (P : PROP) (n : Nat) : PROP := iprop% P → f_impR P (n+1)
ifix f_impPure (n : Nat) : PROP := iprop% ⌜n = 0⌝ → f_impPure (n+1)
icofix f_coImpPure (n : Nat) : PROP := iprop% ⌜n = 0⌝ → f_coImpPure (n+1)
icofix r_coImpPure (n : Nat) : PROP := iprop% ∀ m, ⌜m < n⌝ → ▷ r_coImpPure m
-- A `match` on a constructor reduces, also when it holds the recursive call.
ifix f_sideMatch (n : Nat) : PROP := headOr [f_sideMatch (n+1)]
-- `[∗] (list of calls)` and `[∗list] P ∈ [calls], P`: the lists are related elementwise.
ifix f_bigSep (l : List Nat) : PROP := iprop% [∗] (l.map fun x => f_bigSep [x])
ifix f_listOfCalls (n : Nat) : PROP := iprop% [∗list] P ∈ [f_listOfCalls n, f_listOfCalls (n+1)], P
-- `List.foldr` and `Nat.rec`/`Nat.casesOn` have rules.
ifix f_foldr (l : List Nat) : PROP := l.foldr (fun x acc => iprop(f_foldr [x] ∗ acc)) iprop(emp)
ifix f_natCases (n : Nat) : PROP :=
  Nat.casesOn (motive := fun _ => PROP) n iprop(emp) (fun k => f_natCases k)
-- A recursive helper is unfolded again where it is applied to a constructor (`[n, n+1]`).
ifix f_nested (n : Nat) : PROP := allL f_nested [n, n+1]

-- An `@[irreducible]` helper is still unfolded (`unfold` ignores reducibility).
open scoped Iris.MonotoneFixpoint in
example : IOrder.IMono PROP (fun (f : Nat → PROP) n => opaqueHelper (f (n+1))) := by imono

-- Bodies that use no BI operation still pick up the `[BI PROP]` section variable.
ifix f_loop (n : Nat) : PROP := f_loop (n+1)
ifix f_have (n : Nat) : PROP := have k := n + 1; iprop(f_have k)
ifix f_loopInst [BI PROP] (n : Nat) : PROP := f_loopInst (n+1)
example (n : Nat) : f_loop (PROP := PROP) n = f_loop (n+1) := f_loop.unfold n

-- Non-recursive bodies, also one whose head is an axiom.
ifix f_nonRec (n : Nat) : PROP := iprop% ⌜n = 0⌝
axiom ax {PROP : Type _} [BI PROP] : Nat → PROP
noncomputable ifix f_axiom (n : Nat) : PROP := ax n
example (n : Nat) : f_nonRec (PROP := PROP) n = iprop(⌜n = 0⌝) := f_nonRec.unfold n
example (n : Nat) : f_axiom (PROP := PROP) n = ax n := f_axiom.unfold n
example (n : Nat) : f_nonRec (PROP := PROP) n ⊢ iprop(⌜n = 0⌝) := f_nonRec.unfold_mp n

/-! ## Errors in the body -/

/-- error: Unknown identifier `undefinedThing` -/
#guard_msgs in
ifix e_rec (n : Nat) : PROP := iprop% ▷ e_rec (n+1) ∗ undefinedThing

/-- error: Unknown identifier `undefinedThing` -/
#guard_msgs in
ifix e_nonRec (n : Nat) : PROP := iprop% undefinedThing n
/-- error: Unknown identifier `undefinedThing` -/
#guard_msgs in
ifix e_lostRec (n : Nat) : PROP := iprop% undefinedThing e_lostRec n

end IrisTest.Stress.Bodies
