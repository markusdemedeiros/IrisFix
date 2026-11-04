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

ifix even (n : Nat) : PROP := iprop% ⌜n = 0⌝ ∨ ∃ m, ⌜n = m + 2⌝ ∗ even m

example (n : Nat) : even (PROP := PROP) n = even.pre even n := even.unfold n

example (Φ Ψ : Nat → PROP) : ⊢ □ (∀ n, Φ n -∗ Ψ n) -∗ ∀ n, even.pre Φ n -∗ even.pre Ψ n :=
  even.pre_mono Φ Ψ

example (Φ : Nat → PROP) : ⊢ □ (∀ n, even.pre Φ n -∗ Φ n) -∗ ∀ n, even n -∗ Φ n := even.iter Φ

example (Φ : Nat → PROP) :
    ⊢ □ (∀ n, even.pre (fun m => iprop(Φ m ∧ even m)) n -∗ Φ n) -∗ ∀ n, even n -∗ Φ n :=
  even.ind Φ

-- Three varying parameters.
icofix swap (P : PROP) (n : Nat) (b : Bool) : PROP := iprop% P ∗ ▷ swap P (n + 1) !b

example (P : PROP) (n : Nat) (b : Bool) : swap P n b = swap.pre swap P n b := swap.unfold P n b

example (Φ : PROP → Nat → Bool → PROP) :
    ⊢ □ (∀ P n b, Φ P n b -∗ swap.pre Φ P n b) -∗ ∀ P n b, Φ P n b -∗ swap P n b :=
  swap.coiter Φ

example (Φ : PROP → Nat → Bool → PROP) :
    ⊢ □ (∀ P n b, Φ P n b -∗ swap.pre (fun P n b => iprop(Φ P n b ∨ swap P n b)) P n b) -∗
      ∀ P n b, Φ P n b -∗ swap P n b :=
  swap.coind Φ

example (G : (Nat → PROP) → Nat → PROP) (g : Nat → PROP) (hg : ∀ n, G g n ⊢ g n) :
    ⊢ □ (∀ Φ n, even.pre Φ n -∗ G Φ n) -∗ ∀ n, even n -∗ g n :=
  even.strong_mono G g hg

example (Φ W : Nat → PROP) (hW : ∀ n, iprop(Φ n ∧ even.pre W n) ⊢ W n) :
    ⊢ □ (∀ n, even.pre W n -∗ Φ n) -∗ ∀ n, even n -∗ Φ n :=
  even.ind_wf Φ W hW

example (Φ W : PROP → Nat → Bool → PROP)
    (hW : ∀ P n b, W P n b ⊢ iprop(Φ P n b ∨ swap.pre W P n b)) :
    ⊢ □ (∀ P n b, Φ P n b -∗ swap.pre W P n b) -∗ ∀ P n b, Φ P n b -∗ swap P n b :=
  swap.paco Φ W hW

/-! ## Instances -/

example (n : Nat) : Persistent (even (PROP := PROP) n) := inferInstance
example (n : Nat) : Absorbing (even (PROP := PROP) n) := inferInstance
example [BIAffine PROP] (n : Nat) : Affine (even (PROP := PROP) n) := inferInstance
example (P : PROP) [Absorbing P] (n : Nat) (b : Bool) : Absorbing (swap P n b) := inferInstance

/-! ## `ne` -/

section
variable {α : Type _}

-- A leading instance binder is a fixed parameter.
ifix swapNe [OFE α] (x y : α) : PROP := iprop% ▷ swapNe y x

example [OFE α] {n : Nat} {x x' y y' : α} (hx : x ≡{n}≡ x') (hy : y ≡{n}≡ y') :
    swapNe (PROP := PROP) x y ≡{n}≡ swapNe x' y' :=
  swapNe.ne (fun _ _ hf x x' hx y y' hy => later_ne.ne (hf y y' hy x x' hx)) x x' hx y y' hy

-- A parameter passed on unchanged, after a changing one.
ifix mixed2 [OFE α] (b : Bool) (x : α) : PROP := iprop% ▷ mixed2 (!b) x ∗ mixed2 b x

example [OFE α] (b : Bool) (x : α) : mixed2 (PROP := PROP) b x = mixed2.pre mixed2 b x :=
  mixed2.unfold b x

example [OFE α] (Φ : Bool → α → PROP) :
    ⊢ □ (∀ b x, mixed2.pre Φ b x -∗ Φ b x) -∗ ∀ b x, mixed2 b x -∗ Φ b x :=
  mixed2.iter Φ

example [OFE α] [BIAffine PROP] (x : α) (b : Bool) : Affine (mixed2 (PROP := PROP) b x) :=
  inferInstance

-- A parameter without an OFE after ones with an OFE.
ifix mixedNe [OFE α] (x y : α) (k : Nat) : PROP := iprop% ▷ mixedNe y x k

example [OFE α] (k : Nat) {n : Nat} {x x' y y' : α} (hx : x ≡{n}≡ x') (hy : y ≡{n}≡ y') :
    mixedNe (PROP := PROP) x y k ≡{n}≡ mixedNe x' y' k :=
  mixedNe.ne (fun _ _ hf x x' hx y y' hy k => later_ne.ne (hf y y' hy x x' hx k)) x x' hx y y' hy k
end

end IrisTest.Fixpoint
