/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import IrisFix.BI.Lib.Monotone
public import IrisFix.Std.Order
import all Init.Internal.Order.Basic

/-! # Lattice-based Iris Fixpoints

Entailment (`MonotoneFixpoint`) and reverse entailment (`CoMonotoneFixpoint`) make `PROP` a CCPO,
so `partial_fixpoint` defines least and greatest fixpoints of `BIMono` bodies. Their laws are in
`IrisFix.BI.Lib.Pointwise`. -/

@[expose] public section

namespace Iris
open BI Lean.Order OFE

local bi PROP

variable {PROP : Type _} [BI PROP] {A : Sort _}

namespace MonotoneFixpoint

scoped instance instPartialOrderMonoProp : PartialOrder PROP where
  rel Φ Ψ := Φ ⊢ Ψ
  rel_refl := .rfl
  rel_trans := .trans
  rel_antisymm := (equiv_iff.mpr ⟨·, ·⟩)

theorem sExists_is_sup (c : PROP → Prop) : is_sup c (sExists c) :=
  fun _ => ⟨fun h _ hy => (sExists_intro hy).trans h, sExists_elim⟩

scoped instance instCCPOMonoProp : CCPO PROP where
  has_csup {c} _ := ⟨_, sExists_is_sup c⟩

theorem monotone_of_bimono {F : (A → PROP) → A → PROP} (h : BIMono F) : monotone F :=
  fun Φ Ψ hle x => by
  change F Φ x ⊢ F Ψ x
  iintro H
  iapply (h Φ Ψ) $$ [] %x H
  iintro !> %x H
  have hw : ⊢ Φ x -∗ Ψ x := wand_intro (emp_sep.1.trans (hle x))
  iapply hw $$ [$]

/-- The least fixpoint of a `BIMono` body. -/
noncomputable abbrev lfp (F : (A → PROP) → A → PROP) (h : BIMono F) : A → PROP :=
  fix F (monotone_of_bimono h)

end MonotoneFixpoint

namespace CoMonotoneFixpoint

scoped instance instPartialOrderAntiProp : PartialOrder PROP where
  rel Φ Ψ := Ψ ⊢ Φ
  rel_refl := .rfl
  rel_trans h1 h2 := h2.trans h1
  rel_antisymm h1 h2 := equiv_iff.mpr ⟨h2, h1⟩

theorem sForall_is_sup (c : PROP → Prop) : is_sup c (sForall c) :=
  fun _ => ⟨fun h _ hy => h.trans (sForall_elim hy), sForall_intro⟩

scoped instance instCCPOAntiProp : CCPO PROP where
  has_csup {c} _ := ⟨_, sForall_is_sup c⟩

theorem monotone_of_bimono {F : (A → PROP) → A → PROP} (h : BIMono F) : monotone F :=
  fun Φ Ψ hle x => by
  have hw : ⊢ ∀ x, Ψ x -∗ Φ x := forall_intro fun x => wand_intro (emp_sep.1.trans (hle x))
  change F Ψ x ⊢ F Φ x
  iintro H
  iapply (h Ψ Φ) $$ [] %x H
  iintro !>
  iapply hw

/-- The greatest fixpoint of a `BIMono` body. -/
noncomputable abbrev gfp (F : (A → PROP) → A → PROP) (h : BIMono F) : A → PROP :=
  fix F (monotone_of_bimono h)

end CoMonotoneFixpoint

end Iris
