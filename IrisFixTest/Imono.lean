/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.BI
public import IrisFix.ProofMode.Lib.Fixpoint

/-! Regression tests for the `imono` monotonicity tactic. -/

@[expose] public section
open Iris BI

namespace IrisTest.Imono

local bi PROP

variable {PROP : Type _} [BI PROP]

/-! ## Implication -/

ifix impR (P : PROP) (n : Nat) : PROP := iprop% P → impR P (n+1)
ifix impPure (n : Nat) : PROP := iprop% ∀ m, ⌜m < n⌝ → ▷ impPure m
ifix impBoth (n : Nat) : PROP := iprop% (<pers> ⌜n = 0⌝ → ⌜n = 1⌝) → impBoth (n+1) ∧ emp
icofix coImp (P : PROP) (n : Nat) : PROP := iprop% P → coImp P (n+1)

section
open scoped Iris.MonotoneFixpoint

-- The premise of `→` is a negative position.
/--
error: imono: not monotone, or not covered by an @[imono] rule
PROP : Type u_1
inst✝ : BI PROP
Φ✝ Ψ✝ : Nat → PROP
x✝ : Nat
⊢ ⊢ (□ ∀ x, Φ✝ x -∗ Ψ✝ x) -∗ Ψ✝ (x✝ + 1) -∗ Φ✝ (x✝ + 1)
-/
#guard_msgs in
example : IOrder.IMono PROP (fun (f : Nat → PROP) n => iprop(f (n+1) → emp)) := by imono
end

/-! ## Lists of recursive calls -/

ifix sepLit (n : Nat) : PROP := iprop% [∗] [sepLit n, iprop(▷ sepLit (n+1))]
ifix sepLMap (l : List Nat) : PROP :=
  iprop([∗list] k ↦ P ∈ l.map fun x => sepLMap [x], ▷ P ∗ ⌜k = k⌝)
ifix sepLLit (n : Nat) : PROP := iprop% [∗list] k ↦ P ∈ [sepLLit n, sepLLit (n+2)], P ∗ ⌜k = 0⌝
  monotone_by imono
icofix coSepMap (l : List Nat) : PROP := iprop% [∗] (l.map fun x => coSepMap [x+1])

section
open scoped Iris.MonotoneFixpoint

-- A `match` on a list of calls that does not reduce: the two sides cannot be split together.
/--
error: imono: cannot split this `match`/`if` on both sides: its discriminants mention the recursive call
PROP : Type u_1
inst✝ : BI PROP
Φ✝ Ψ✝ : List Nat → PROP
x✝ : List Nat
⊢ ⊢
    (□ ∀ x, Φ✝ x -∗ Ψ✝ x) -∗
      (match List.map (fun x => Φ✝ [x]) x✝ with
        | [] => emp
        | P :: tail => P) -∗
        match List.map (fun x => Ψ✝ [x]) x✝ with
        | [] => emp
        | P :: tail => P
-/
#guard_msgs in
example : IOrder.IMono PROP (fun (f : List Nat → PROP) l =>
    match l.map fun x => f [x] with | [] => iprop(emp) | P :: _ => P) := by imono
end

/-! ## Recursive helpers and recursors -/

ifix foldl (l : List Nat) : PROP := l.foldl (fun acc x => iprop(acc ∗ ▷ foldl [x])) iprop(True)
ifix natRec (n : Nat) : PROP :=
  Nat.rec (motive := fun _ => PROP) iprop(emp) (fun k acc => iprop(natRec k ∗ ▷ acc)) n

def below (g : Nat → PROP) : Nat → PROP
  | 0 => iprop(emp)
  | n+1 => iprop(g n ∗ below g n)

-- At a numeral, a recursive helper is unfolded until it stops.
ifix belowLit (n : Nat) : PROP := iprop% below belowLit 3 ∗ ▷ belowLit (n+1)

section
open scoped Iris.MonotoneFixpoint

-- Other recursors need a rule.
/--
error: imono: no rule for the recursor List.rec; add an @[imono] rule for it, such as `IMonoPred.natRec`
-/
#guard_msgs in
example : IOrder.IMono PROP (fun (f : Nat → PROP) n =>
    List.rec (motive := fun _ => PROP) iprop(emp) (fun x _ acc => iprop(f x ∗ acc)) [n]) := by
  imono
end

/-! ## Goal shapes -/

example : BIMono (PROP := PROP) (fun (f : Nat → PROP) n => iprop(⌜n = 0⌝ → f (n+1))) := by imono

-- `monotone_by` sees the BI statement, for a manual proof.
ifix manual (n : Nat) : PROP := iprop% ▷ manual (n+1)
  monotone_by
    intro Φ Ψ
    iintro #H %n HP !>
    iapply H $$ HP
icofix manualCo (n : Nat) : PROP := iprop% ▷ manualCo (n+1)
  monotone_by
    intro Φ Ψ
    iintro #H %n HP !>
    iapply H $$ HP

end IrisTest.Imono
