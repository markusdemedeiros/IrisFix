/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import IrisFix.BI.Lib.FixpointBanach

@[expose] public section
open Iris BI OFE

namespace IrisTest.FixpointBanach

local bi PROP

variable {PROP : Type _} [BI PROP]

/-! ## The generic laws are the unary laws of `FixpointBanach` -/

section
variable {A : Type _} (F : (A → PROP) → A → PROP) [Contractive F]

example : (∀ Φ, (∀ x, Persistent (Φ x)) → (∀ x, Persistent (F Φ x))) →
    ∀ x, Persistent (fixpoint F x) :=
  Banach.fixpoint_persistent (PROP := PROP) F (fixpoint_unfold F.toContractiveHom)

example : (∀ Φ, (∀ x, Absorbing (Φ x)) → (∀ x, Absorbing (F Φ x))) →
    ∀ x, Absorbing (fixpoint F x) :=
  Banach.fixpoint_absorbing (PROP := PROP) F (fixpoint_unfold F.toContractiveHom)

example : (∀ Φ, (∀ x, Affine (Φ x)) → (∀ x, Affine (F Φ x))) → ∀ x, Affine (fixpoint F x) :=
  Banach.fixpoint_affine (PROP := PROP) F (fixpoint_unfold F.toContractiveHom)

example : (∀ Φ, (∀ x, Persistent (Φ x)) → (∀ x, Absorbing (Φ x)) →
      (∀ x, Persistent (F Φ x) ∧ Absorbing (F Φ x))) →
    ∀ x, Persistent (fixpoint F x) ∧ Absorbing (fixpoint F x) :=
  Banach.fixpoint_persistent_absorbing (PROP := PROP) F (fixpoint_unfold F.toContractiveHom)

example : (∀ Φ, (∀ x, Persistent (Φ x)) → (∀ x, Affine (Φ x)) →
      (∀ x, Persistent (F Φ x) ∧ Affine (F Φ x))) →
    ∀ x, Persistent (fixpoint F x) ∧ Affine (fixpoint F x) :=
  Banach.fixpoint_persistent_affine (PROP := PROP) F (fixpoint_unfold F.toContractiveHom)
end

/-! ## Two arguments -/

section
variable (F : (Nat → Bool → PROP) → Nat → Bool → PROP) [Contractive F]

example : (∀ Φ, (∀ n b, Persistent (Φ n b)) → ∀ n b, Persistent (F Φ n b)) →
    ∀ n b, Persistent (fixpoint F n b) :=
  Banach.fixpoint_persistent (PROP := PROP) F (fixpoint_unfold F.toContractiveHom)

example : (∀ Φ, (∀ n b, Persistent (Φ n b)) → (∀ n b, Absorbing (Φ n b)) →
      ∀ n b, Persistent (F Φ n b) ∧ Absorbing (F Φ n b)) →
    ∀ n b, Persistent (fixpoint F n b) ∧ Absorbing (fixpoint F n b) :=
  Banach.fixpoint_persistent_absorbing (PROP := PROP) F (fixpoint_unfold F.toContractiveHom)
end

-- A guarded body: `Persistent` at every point, at two arguments.
def body (Φ : Nat → Bool → PROP) (n : Nat) (b : Bool) : PROP := iprop(□ ▷ Φ (n + 1) !b)

instance [BILaterContractive PROP] : Contractive (body (PROP := PROP)) where
  distLater_dist h n b :=
    intuitionistically_ne.ne (Contractive.distLater_dist fun m hm => h m hm (n + 1) !b)

example [BILaterContractive PROP] (n : Nat) (b : Bool) :
    Persistent (fixpoint (body (PROP := PROP)) n b) := by
  have h := Banach.fixpoint_persistent (PROP := PROP) (body (PROP := PROP))
    (fixpoint_unfold (body (PROP := PROP)).toContractiveHom) fun Φ _ => by
    intro n b
    unfold body
    infer_instance
  exact h n b

end IrisTest.FixpointBanach
