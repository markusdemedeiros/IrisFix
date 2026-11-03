/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.BI
public import IrisFix.ProofMode.Lib.Fixpoint

@[expose] public section
open Iris BI OFE

namespace IrisTest.Fixpoint

local bi PROP

variable {PROP : Type _} [BI PROP]

ifix even (n : Nat) : PROP := iprop(⌜n = 0⌝ ∨ ∃ m, ⌜n = m + 2⌝ ∗ even m)

example (n : Nat) : even (PROP := PROP) n = even.pre even n := even.unfold n

example (Φ Ψ : Nat → PROP) : ⊢ □ (∀ n, Φ n -∗ Ψ n) -∗ ∀ n, even.pre Φ n -∗ even.pre Ψ n :=
  even.pre_mono Φ Ψ

example (Φ : Nat → PROP) : ⊢ □ (∀ n, even.pre Φ n -∗ Φ n) -∗ ∀ n, even n -∗ Φ n := even.iter Φ

example (Φ : Nat → PROP) :
    ⊢ □ (∀ n, even.pre (fun m => iprop(Φ m ∧ even m)) n -∗ Φ n) -∗ ∀ n, even n -∗ Φ n :=
  even.ind Φ

-- A fixed parameter and two varying ones.
icofix swap (P : PROP) (n : Nat) (b : Bool) : PROP := iprop(P ∗ ▷ swap P (n + 1) !b)

example (P : PROP) (n : Nat) (b : Bool) : swap P n b = swap.pre P (swap P) n b := swap.unfold P n b

example (P : PROP) (Φ : Nat → Bool → PROP) :
    ⊢ □ (∀ n b, Φ n b -∗ swap.pre P Φ n b) -∗ ∀ n b, Φ n b -∗ swap P n b :=
  swap.coiter P Φ

example (P : PROP) (Φ : Nat → Bool → PROP) :
    ⊢ □ (∀ n b, Φ n b -∗ swap.pre P (fun n b => iprop(Φ n b ∨ swap P n b)) n b) -∗
      ∀ n b, Φ n b -∗ swap P n b :=
  swap.coind P Φ

example (G : (Nat → PROP) → Nat → PROP) (g : Nat → PROP) (hg : ∀ n, G g n ⊢ g n) :
    ⊢ □ (∀ Φ n, even.pre Φ n -∗ G Φ n) -∗ ∀ n, even n -∗ g n :=
  even.strong_mono G g hg

example (Φ W : Nat → PROP) (hW : ∀ n, iprop(Φ n ∧ even.pre W n) ⊢ W n) :
    ⊢ □ (∀ n, even.pre W n -∗ Φ n) -∗ ∀ n, even n -∗ Φ n :=
  even.ind_wf Φ W hW

example (P : PROP) (Φ W : Nat → Bool → PROP) (hW : ∀ n b, W n b ⊢ iprop(Φ n b ∨ swap.pre P W n b)) :
    ⊢ □ (∀ n b, Φ n b -∗ swap.pre P W n b) -∗ ∀ n b, Φ n b -∗ swap P n b :=
  swap.paco P Φ W hW

/-! ## Instances -/

example (n : Nat) : Persistent (even (PROP := PROP) n) := inferInstance
example (n : Nat) : Absorbing (even (PROP := PROP) n) := inferInstance
example [BIAffine PROP] (n : Nat) : Affine (even (PROP := PROP) n) := inferInstance
example (P : PROP) [Absorbing P] (n : Nat) (b : Bool) : Absorbing (swap P n b) := inferInstance

/-! ## `ne` -/

section
variable {α : Type _}

ifix swapNe [OFE α] (x y : α) : PROP := iprop(▷ swapNe y x)

example [OFE α] {n : Nat} {x x' y y' : α} (hx : x ≡{n}≡ x') (hy : y ≡{n}≡ y') :
    swapNe (PROP := PROP) x y ≡{n}≡ swapNe x' y' :=
  swapNe.ne (fun _ hf n x x' hx y y' hy => later_ne.ne (hf n y y' hy x x' hx)) n x x' hx y y' hy
end

end IrisTest.Fixpoint
