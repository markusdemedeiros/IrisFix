/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import IrisFix.Algebra.Approx
public import Iris.BI

@[expose] public section
open Iris BI OFE Lean.Order Approx

namespace IrisTest.Approx

local bi PROP

variable {PROP : Type _} [BI PROP] [BILaterContractive PROP] [Inhabited PROP]

/-! Guarded fixpoints by `partial_fixpoint` on approximations, with a fixed parameter `k`. -/

-- One varying parameter.
def body1 (k : Nat) (Φ : Nat → PROP) (n : Nat) : PROP := iprop% ▷ Φ (n + k)

instance (k : Nat) : Contractive (body1 (PROP := PROP) k) where
  distLater_dist h n := Contractive.distLater_dist fun m hm => h m hm (n + k)

noncomputable def approx1 (k : Nat) : Approx (Nat → PROP) := lift (body1 k) (approx1 k)
partial_fixpoint monotonicity fun _ _ h => lift_mono _ _ _ h

example (k : Nat) : get (approx1 (PROP := PROP) k) = fixpoint (body1 k) :=
  get_eq_fixpoint (body1 k) (approx1.eq_1 k).symm

-- Two curried varying parameters.
def body2 (k : Nat) (Φ : Nat → Bool → PROP) (n : Nat) (b : Bool) : PROP := iprop% ▷ Φ (n + k) !b

instance (k : Nat) : Contractive (body2 (PROP := PROP) k) where
  distLater_dist h n b := Contractive.distLater_dist fun m hm => h m hm (n + k) !b

noncomputable def approx2 (k : Nat) : Approx (Nat → Bool → PROP) :=
  lift (body2 k) (approx2 k)
partial_fixpoint monotonicity fun _ _ h => lift_mono _ _ _ h

example (k : Nat) : get (approx2 (PROP := PROP) k) = fixpoint (body2 k) :=
  get_eq_fixpoint (body2 k) (approx2.eq_1 k).symm

-- `wp`-shaped: three varying parameters, the last a predicate.
def body3 (k : Nat) (Ψ : Nat → Bool → (Nat → PROP) → PROP) (n : Nat) (b : Bool)
    (Φ : Nat → PROP) : PROP :=
  iprop(Φ n ∨ ▷ Ψ (n + k) (!b) fun m => Φ (m + 1))

instance (k : Nat) : Contractive (body3 (PROP := PROP) k) where
  distLater_dist h n b Φ :=
    or_ne.ne .rfl (Contractive.distLater_dist fun m hm => h m hm (n + k) (!b) fun m => Φ (m + 1))

noncomputable def approx3 (k : Nat) : Approx (Nat → Bool → (Nat → PROP) → PROP) :=
  lift (body3 k) (approx3 k)
partial_fixpoint monotonicity fun _ _ h => lift_mono _ _ _ h

example (k : Nat) : get (approx3 (PROP := PROP) k) = fixpoint (body3 k) :=
  get_eq_fixpoint (body3 k) (approx3.eq_1 k).symm

end IrisTest.Approx
