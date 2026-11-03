/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import IrisFix.BI.Lib.Fixpoint

/-! # Iris Banach fixpoints

The laws of the Banach fixpoint, stated with `PointwiseLifting.all`: a property holds at every
point of a fixpoint `f = F f` if `F` preserves it at every point. -/

@[expose] public section

namespace Iris
open BI OFE

local bi PROP

namespace Banach
open PointwiseLifting (all all_imp all_const)
variable {PROP : Type _} [BI PROP] {Pred : Type _} [COFE Pred] [Inhabited Pred]
  [PointwiseLifting PROP Pred] [PointwiseLiftingLim PROP Pred]

/-- `C` holds at every point of a fixpoint, if `F` preserves it, `C` survives limits, and some
`c` satisfies it. -/
theorem fixpoint_all {C : PROP → Prop} (hC : LimitPreserving C) {c : PROP} (hc : C c)
    (F : Pred → Pred)
    [Contractive F] {f : Pred} (hf : f = F f) (h : ∀ Φ, all C Φ → all C (F Φ)) : all C f := by
  rw [fixpoint_unique (f := F.toContractiveHom) hf]
  exact ContractiveHom.fixpoint_ind ⟨F, inferInstance⟩ (all C) (PointwiseLifting.map (fun _ => c)
    default) (all_const hc _) h (PointwiseLiftingLim.all_lim hC)

variable (F : Pred → Pred) [Contractive F] {f : Pred} (hf : f = F f)
include hf

theorem fixpoint_persistent :
    (∀ Φ, all (B := PROP) Persistent Φ → all (B := PROP) Persistent (F Φ)) →
      all (B := PROP) Persistent f :=
  fixpoint_all (C := Persistent) (limitPreserving_persistent id) (c := iprop(emp)) inferInstance F
    hf

theorem fixpoint_absorbing :
    (∀ Φ, all (B := PROP) Absorbing Φ → all (B := PROP) Absorbing (F Φ)) →
      all (B := PROP) Absorbing f :=
  fixpoint_all (C := Absorbing) (limitPreserving_absorbing id) (c := iprop(True)) inferInstance F hf

theorem fixpoint_affine :
    (∀ Φ, all (B := PROP) Affine Φ → all (B := PROP) Affine (F Φ)) →
      all (B := PROP) Affine f :=
  fixpoint_all (C := Affine) (limitPreserving_affine id) (c := iprop(emp)) inferInstance F hf

theorem fixpoint_persistent_absorbing
    (h : ∀ Φ, all (B := PROP) Persistent Φ → all (B := PROP) Absorbing Φ →
      all (B := PROP) (fun P => Persistent P ∧ Absorbing P) (F Φ)) :
    all (B := PROP) (fun P => Persistent P ∧ Absorbing P) f :=
  fixpoint_all (C := fun P => Persistent P ∧ Absorbing P)
    ((limitPreserving_persistent id).and (limitPreserving_absorbing id))
    (c := iprop(True)) ⟨inferInstance, inferInstance⟩ F hf
    fun Φ hΦ => h Φ (all_imp (fun _ h => h.1) hΦ) (all_imp (fun _ h => h.2) hΦ)

theorem fixpoint_persistent_affine
    (h : ∀ Φ, all (B := PROP) Persistent Φ → all (B := PROP) Affine Φ →
      all (B := PROP) (fun P => Persistent P ∧ Affine P) (F Φ)) :
    all (B := PROP) (fun P => Persistent P ∧ Affine P) f :=
  fixpoint_all (C := fun P => Persistent P ∧ Affine P)
    ((limitPreserving_persistent id).and (limitPreserving_affine id))
    (c := iprop(emp)) ⟨inferInstance, inferInstance⟩ F hf
    fun Φ hΦ => h Φ (all_imp (fun _ h => h.1) hΦ) (all_imp (fun _ h => h.2) hΦ)

end Banach

end Iris
