/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import IrisFix.BI.Lib.Monotone
public import IrisFix.Std.Order
public import IrisFix.Std.PointwiseLifting
import all Init.Internal.Order.Basic

/-! # Iris fixpoints

`partial_fixpoint` takes fixpoints in a CCPO `Pred`. Here `Pred` is a family of propositions
(`PROP`, `A → PROP`, …), and each class below lifts one notion from `PROP` to `Pred`, a point at a
time:

* `IOrder PROP Pred`: `a ⊑ᵢ b`, the order of `Pred`, inside the BI. For induction.
* `IMeet PROP Pred`: `a ⊓ᵢ b`, the binary meet of `Pred`. For strong induction.
* `INe Pred` (in `IrisFix.Std.Order`): `ne n`, agreement up to `n`, jointly in the arguments that
  have OFEs.

Entailment (`MonotoneFixpoint`) and reverse entailment (`CoMonotoneFixpoint`) make `PROP` a CCPO,
so `partial_fixpoint` defines least and greatest fixpoints. `PROP` is an instance of every class,
for `-∗` and `∧` (`MonotoneFixpoint`) and for the reverse `-∗` and `∨` (`CoMonotoneFixpoint`). A
law for the least fixpoint, in the reverse order, is the law for the greatest fixpoint.

Every other instance is the `PROP` instance, lifted through the arguments of `Pred` by a
`PointwiseLifting` (`IrisFix.Std.PointwiseLifting`): `meet` by `zip`, and `⊑ᵢ` by
`IPointwiseLifting.irel`, which quantifies with the BI's `∀`. The instance laws use the lifting
directly: `all C a` for `C` at every point, and `map m a` for `m` at every point. `INe` follows
the same pattern by its own `Pi` instances: it has no `PROP` to name the base of the lifting. All
the operations unfold, at concrete instances, to the plain curried statements. -/

@[expose] public section

namespace Iris
open BI Lean.Order

local bi PROP

/-! ## Embedding classes
The classes in this section represent different ways that `PROP` lifts to `Pred`.
The canonical example to keep in mind is families of propositions `Pred := A → PROP`: the classes
here outline how different aspects of `PROP` may lift to families of propositions.-/

/-- The order `le` embeds into `PROP` as an Iris proposition. -/
class IOrder (PROP : Type _) [BI PROP] (Pred : Type _) [CCPO Pred] where
  le : Pred → Pred → PROP
  rel_iff {a b : Pred} : a ⊑ b ↔ ⊢ le a b
  trans {a b c : Pred} : ⊢ le a b -∗ le b c -∗ le a c
  csup_le {c : Pred → Prop} (hc : chain c) {R : PROP} {g : Pred} :
    (∀ f, c f → R ⊢ le f g) → R ⊢ le (CCPO.csup hc) g

/-- The order of `Pred`, inside the BI `bi%`. -/
macro:50 a:term:51 " ⊑ᵢ " b:term:51 : term => ``(IOrder.le (PROP := bi%) $a $b)

/-- The binary meet `Pred` is compatible with an embedding of a CCPO into Iris. -/
class IMeet (PROP : Type _) [BI PROP] (Pred : Type _) [CCPO Pred] [IOrder PROP Pred] where
  meet : Pred → Pred → Pred
  meet_l {a b : Pred} : meet a b ⊑ a
  meet_r {a b : Pred} : meet a b ⊑ b
  meet_intro {a b c : Pred} :
    ⊢ IOrder.le (PROP := PROP) a b ∧ IOrder.le a c -∗ IOrder.le a (meet b c)

/-- The binary meet of `Pred`, for the BI `bi%`. -/
macro:69 a:term:70 " ⊓ᵢ " b:term:70 : term => ``(IMeet.meet (PROP := bi%) $a $b)

open IOrder IMeet INe

/-! ## Functions, pointwise -/

section Pi
variable {PROP : Type _} [BI PROP] {ι : Type _} {β : ι → Type _}
open PointwiseLifting (rel rel_mono rel_and rel_forall rel_map rel_diag rel_zip_l rel_zip_r map_id
  zip)
open PointwiseLiftingLe (le_iff)

/-- Relations into `PROP` lift to `Pred`, with the BI's `∀` over the points. -/
class IPointwiseLifting (PROP : Type _) [BI PROP] [CCPO PROP] (Pred : Type _) [CCPO Pred]
    [PointwiseLifting PROP Pred] where
  irel : (PROP → PROP → PROP) → Pred → Pred → PROP
  irel_valid {R : PROP → PROP → PROP} {a b : Pred} : (⊢ irel R a b) ↔ rel (fun x y => ⊢ R x y) a b
  irel_trans {R S T : PROP → PROP → PROP} (h : ∀ x y z, ⊢ R x y -∗ S y z -∗ T x z) {a b c : Pred} :
    ⊢ irel R a b -∗ irel S b c -∗ irel T a c
  irel_zip {R S T : PROP → PROP → PROP} {f : PROP → PROP → PROP}
    (h : ∀ x y z, ⊢ R x y ∧ S x z -∗ T x (f y z)) {a b c : Pred} :
    ⊢ irel R a b ∧ irel S a c -∗ irel T a (zip f b c)
  irel_csup {R : PROP → PROP → PROP}
    (hR : ∀ {c : PROP → Prop} (hc : chain c) {Q g : PROP}, (∀ f, c f → Q ⊢ R f g) →
      Q ⊢ R (CCPO.csup hc) g)
    {c : Pred → Prop} (hc : chain c) {Q : PROP} {g : Pred} :
    (∀ f, c f → Q ⊢ irel R f g) → Q ⊢ irel R (CCPO.csup hc) g

open IPointwiseLifting (irel irel_valid irel_trans irel_zip irel_csup)

instance IPointwiseLifting.instBase [CCPO PROP] : IPointwiseLifting PROP PROP where
  irel R := R
  irel_valid := .rfl
  irel_trans h := h _ _ _
  irel_zip h := h _ _ _
  irel_csup hR := hR

instance IPointwiseLifting.instPi [CCPO PROP] [∀ x, CCPO (β x)]
    [∀ x, PointwiseLifting PROP (β x)] [∀ x, IPointwiseLifting PROP (β x)] :
    IPointwiseLifting PROP (∀ x, β x) where
  irel R a b := iprop(∀ x, irel R (a x) (b x))
  irel_valid := ⟨fun h x => irel_valid.1 (h.trans (forall_elim x)),
    fun h => forall_intro fun x => irel_valid.2 (h x)⟩
  irel_trans h := by
    intro a b c
    iintro Hab Hbc %x
    iapply irel_trans h $$ [Hab] [Hbc]
    · iapply Hab
    · iapply Hbc
  irel_zip h := by
    intro a b c
    iintro H %x
    iapply irel_zip h
    isplit
    · icases H with ⟨H, -⟩; iapply H
    · icases H with ⟨-, H⟩; iapply H
  irel_csup hR := by
    intro c hc Q g hall
    refine forall_intro fun x => ?_
    rw [← fun_csup_eq]
    exact irel_csup hR _ fun v ⟨f, hf, hv⟩ => hv ▸ (hall f hf).trans (forall_elim x)

/-- The order of a pointwise lifting: the order of `PROP`, at every point. -/
instance (priority := low) IOrder.ofLifting [CCPO PROP] [IOrder PROP PROP] {Pred : Type _}
    [CCPO Pred] [PointwiseLifting PROP Pred] [PointwiseLiftingLe PROP Pred]
    [IPointwiseLifting PROP Pred] : IOrder PROP Pred where
  le := irel (IOrder.le (PROP := PROP) (Pred := PROP))
  rel_iff := by
    intro a b
    rw [le_iff (B := PROP), irel_valid]
    exact ⟨rel_mono fun _ _ => rel_iff.1, rel_mono fun _ _ => rel_iff.2⟩
  trans := irel_trans (R := le) (S := le) (T := le) fun _ _ _ => trans
  csup_le := irel_csup fun hc => csup_le hc

/-- The meet of a pointwise lifting: the meet of `PROP`, at every point. -/
instance (priority := low) IMeet.ofLifting [CCPO PROP] [IOrder PROP PROP] [IMeet PROP PROP]
    {Pred : Type _} [CCPO Pred] [PointwiseLifting PROP Pred] [PointwiseLiftingLe PROP Pred]
    [IPointwiseLifting PROP Pred] : IMeet PROP Pred where
  meet := zip (IMeet.meet (PROP := PROP) (Pred := PROP))
  meet_l := (le_iff (B := PROP)).2 (rel_zip_l (fun _ _ => meet_l) _ _)
  meet_r := (le_iff (B := PROP)).2 (rel_zip_r (fun _ _ => meet_r) _ _)
  meet_intro := irel_zip (R := le) (S := le) (T := le) (f := meet PROP) fun _ _ _ => meet_intro

end Pi

/-! ## `PROP`, in both orders -/

namespace MonotoneFixpoint
variable {PROP : Type _} [BI PROP]

scoped instance instPartialOrderMonoProp : PartialOrder PROP where
  rel Φ Ψ := Φ ⊢ Ψ
  rel_refl := .rfl
  rel_trans := .trans
  rel_antisymm := (equiv_iff.mpr ⟨·, ·⟩)

theorem sExists_is_sup (c : PROP → Prop) : is_sup c (sExists c) :=
  fun _ => ⟨fun h _ hy => (sExists_intro hy).trans h, sExists_elim⟩

scoped instance instCCPOMonoProp : CCPO PROP where
  has_csup {c} _ := ⟨_, sExists_is_sup c⟩

scoped instance instIOrderMonoProp : IOrder PROP PROP where
  le P Q := iprop(P -∗ Q)
  rel_iff := ⟨entails_wand, wand_entails⟩
  trans := by
    intro P Q R
    iintro HPQ HQR HP
    iapply HQR
    iapply HPQ $$ HP
  csup_le hc := fun hall => wand_intro <| sep_symm.trans <| wand_elim <|
    ((CCPO.csup_spec hc _).2 fun f hf => wand_intro <| sep_symm.trans <| wand_elim (hall f hf) :)

scoped instance instIMeetMonoProp : IMeet PROP PROP where
  meet P Q := iprop(P ∧ Q)
  meet_l := and_elim_l
  meet_r := and_elim_r
  meet_intro := by
    intro P Q R
    dsimp only [IOrder.le]
    iintro H HP
    isplit
    · icases H with ⟨H, -⟩; iapply H $$ HP
    · icases H with ⟨-, H⟩; iapply H $$ HP

scoped instance instINeMonoProp : INe PROP where
  ne n P Q := P ≡{n}≡ Q
  ne_csup hc₁ hc₂ h := by
    rw [is_sup_unique (CCPO.csup_spec hc₁) (sExists_is_sup _),
      is_sup_unique (CCPO.csup_spec hc₂) (sExists_is_sup _)]
    exact sExists_ne h

end MonotoneFixpoint

namespace CoMonotoneFixpoint
variable {PROP : Type _} [BI PROP]

scoped instance instPartialOrderAntiProp : PartialOrder PROP where
  rel Φ Ψ := Ψ ⊢ Φ
  rel_refl := .rfl
  rel_trans h1 h2 := h2.trans h1
  rel_antisymm h1 h2 := equiv_iff.mpr ⟨h2, h1⟩

theorem sForall_is_sup (c : PROP → Prop) : is_sup c (sForall c) :=
  fun _ => ⟨fun h _ hy => h.trans (sForall_elim hy), sForall_intro⟩

scoped instance instCCPOAntiProp : CCPO PROP where
  has_csup {c} _ := ⟨_, sForall_is_sup c⟩

scoped instance instIOrderAntiProp : IOrder PROP PROP where
  le P Q := iprop(Q -∗ P)
  rel_iff := ⟨entails_wand, wand_entails⟩
  trans := by
    intro P Q R
    iintro HQP HRQ HR
    iapply HQP
    iapply HRQ $$ HR
  csup_le hc := fun hall => wand_intro <|
    ((CCPO.csup_spec hc _).2 fun f hf => wand_elim (hall f hf) :)

scoped instance instIMeetAntiProp : IMeet PROP PROP where
  meet P Q := iprop(P ∨ Q)
  meet_l := or_intro_l
  meet_r := or_intro_r
  meet_intro := by
    intro P Q R
    dsimp only [IOrder.le]
    iintro H (HP | HP)
    · icases H with ⟨H, -⟩; iapply H $$ HP
    · icases H with ⟨-, H⟩; iapply H $$ HP

scoped instance instINeAntiProp : INe PROP where
  ne n P Q := P ≡{n}≡ Q
  ne_csup hc₁ hc₂ h := by
    rw [is_sup_unique (CCPO.csup_spec hc₁) (sForall_is_sup _),
      is_sup_unique (CCPO.csup_spec hc₂) (sForall_is_sup _)]
    exact sForall_ne h

end CoMonotoneFixpoint

/-! ## The laws -/

namespace IOrder

section Laws
variable {PROP : Type _} [BI PROP] {Pred : Type _} [CCPO Pred] [IOrder PROP Pred]

/-- `F` is monotone inside the BI. -/
def IMono (PROP : Type _) [BI PROP] [IOrder PROP Pred] (F : Pred → Pred) : Prop :=
  ∀ Φ Ψ : Pred, ⊢ □ (Φ ⊑ᵢ Ψ) -∗ F Φ ⊑ᵢ F Ψ

variable {F : Pred → Pred}

theorem monotone_of_imono (hF : IMono PROP F) : monotone F := fun Φ Ψ hΦΨ =>
    (rel_iff (PROP := PROP)).2 <| by
  iapply hF Φ Ψ
  iintro !>
  iapply rel_iff.1 hΦΨ

/-- Iris induction, in the order `⊑ᵢ`. -/
theorem fix_iter (hF : IMono PROP F) (Φ : Pred) :
    ⊢ □ (F Φ ⊑ᵢ Φ) -∗ fix F (monotone_of_imono hF) ⊑ᵢ Φ :=
  entails_wand <| fix_induct _ (fun f => iprop(□ (F Φ ⊑ᵢ Φ)) ⊢ f ⊑ᵢ Φ)
    (fun _ hc => csup_le hc) fun f ih => by
  iintro #H
  iapply trans (b := F Φ) $$ [] H
  iapply hF f Φ
  iintro !>
  iapply ih $$ H

/-- The fixpoint is below every prefixpoint `g` of a larger body `G`. -/
theorem fix_strong_mono (hF : IMono PROP F) (G : Pred → Pred) (g : Pred) (hg : G g ⊑ g) :
    ⊢ □ (∀ Φ, F Φ ⊑ᵢ G Φ) -∗ fix F (monotone_of_imono hF) ⊑ᵢ g := by
  iintro #H
  iapply fix_iter hF
  iintro !>
  iapply trans (b := G g) $$ [] []
  · iapply H
  · iapply rel_iff.1 hg

variable [IMeet PROP Pred]

/-- Strong induction: the hypothesis also gets the fixpoint, through `meet`. -/
theorem fix_ind (hF : IMono PROP F) (Φ : Pred) :
    ⊢ □ (F (Φ ⊓ᵢ fix F (monotone_of_imono hF)) ⊑ᵢ Φ) -∗ fix F (monotone_of_imono hF) ⊑ᵢ Φ := by
  have hfix := monotone_of_imono hF
  iintro #H
  iapply trans (b := Φ ⊓ᵢ fix F hfix) $$ [] []
  · iapply fix_iter hF
    iintro !>
    iapply meet_intro
    isplit
    · iexact H
    -- `meet Φ (fix F)` is below `fix F`, so `F` of it is below `F (fix F) = fix F`.
    · iapply trans (b := F (fix F hfix)) $$ [] []
      · iapply hF (Φ ⊓ᵢ fix F hfix) (fix F hfix)
        iintro !>
        iapply rel_iff.1 meet_r
      · iapply rel_iff.1 (PartialOrder.rel_of_eq (fix_eq hfix).symm)
  · iapply rel_iff.1 meet_l

/-- Well-founded induction, for `W` above `meet Φ (F W)`. In the reverse order, this is
parameterized coinduction. -/
theorem fix_ind_wf (hF : IMono PROP F) (Φ W : Pred) (hW : Φ ⊓ᵢ F W ⊑ W) :
    ⊢ □ (F W ⊑ᵢ Φ) -∗ fix F (monotone_of_imono hF) ⊑ᵢ Φ := by
  have hfix := monotone_of_imono hF
  iintro #H
  -- `fix F = F (fix F)`, which is below `F W` since `fix F` is below `W`.
  iapply trans (b := F (fix F hfix)) $$ [] []
  · iapply rel_iff.1 (PartialOrder.rel_of_eq (fix_eq hfix))
  iapply trans (b := F W) $$ [] H
  iapply hF (fix F hfix) W
  iintro !>
  iapply fix_iter hF
  iintro !>
  iapply trans (b := Φ ⊓ᵢ F W) $$ [] []
  · iapply meet_intro
    isplit
    · iexact H
    · iapply rel_iff.1 PartialOrder.rel_refl
  · iapply rel_iff.1 hW

end Laws

/-! ## Instances

An instance at every point is `fix F ⊑ E` for a constant `E`, or `fix F ⊑ m (fix F)` for `m` a
`map` of an operator, which is monotone by `PointwiseLifting.map_mono`: Park induction (`fix_le_of`,
`fix_le_map`). -/

private theorem true_wand_elim {PROP : Type _} [BI PROP] (P : PROP) : iprop(True -∗ P) ⊢ P := by
  iintro H
  iapply H
  ipureintro
  trivial

private theorem absorbing_true_wand {PROP : Type _} [BI PROP] (P : PROP) [Absorbing P] :
    P ⊢ iprop(True -∗ P) := by
  iintro H -
  iexact H

/-! ### The instances, at every point -/

open PointwiseLifting (all all_imp all_and all_forall map all_le map_const fix_all)

section Lfp
open MonotoneFixpoint
variable (PROP : Type _) [BI PROP] {Pred : Type _} [CCPO Pred] [PointwiseLifting PROP Pred]
  [PointwiseLiftingLe PROP Pred]
  {F : Pred → Pred} (hF : monotone F)
include hF

theorem lfp_affine
    (h : all (B := PROP) Affine (F (map (fun _ : PROP => iprop(emp)) (fix F hF)))) :
    all (B := PROP) Affine (fix F hF) := by
  have hC (P : PROP) : Affine P ↔ P ⊑ (fun _ => iprop(emp)) P := ⟨fun h => h.affine, fun h => ⟨h⟩⟩
  -- Park induction at the constant `emp`.
  exact (all_le hC _).2 <| fix_le_of hF <|
    PartialOrder.rel_trans ((all_le hC _).1 h) (PartialOrder.rel_of_eq map_const)

theorem lfp_absorbing
    (h : all (B := PROP) Absorbing (F (map (fun P : PROP => iprop(True -∗ P)) (fix F hF)))) :
    all (B := PROP) Absorbing (fix F hF) :=
  fix_all hF (fun _ _ => wand_mono_right)
    (fun P => ⟨fun _ => absorbing_true_wand P, fun h => ⟨sep_symm.trans (wand_elim h)⟩⟩)
    (all_forall true_wand_elim _) h

theorem lfp_persistent_affine
    (hA : all (B := PROP) Affine (F (map (fun P : PROP => iprop(□ P)) (fix F hF))))
    (hP : all (B := PROP) Persistent (F (map (fun P : PROP => iprop(□ P)) (fix F hF)))) :
    all (B := PROP) Persistent (fix F hF) :=
  all_imp (fun _ h => h.2) <| fix_all hF (C := fun P => Affine P ∧ Persistent P)
    (fun _ _ => intuitionistically_mono)
    (fun P => ⟨fun ⟨hA, hP⟩ => (@intuitionistically_of_intuitionistic _ _ P hA hP).2,
      fun h => ⟨⟨h.trans Affine.affine⟩, ⟨h.trans persistently_of_intuitionistically⟩⟩⟩)
    (all_forall (fun _ => intuitionistically_elim) _) (all_and hA hP)

theorem lfp_persistent_absorbing (hA : all (B := PROP) Absorbing (fix F hF))
    (hP : all (B := PROP) Persistent (F (map (fun P : PROP => iprop(<pers> P)) (fix F hF)))) :
    all (B := PROP) Persistent (fix F hF) :=
  fix_all hF (fun _ _ => persistently_mono) (fun _ => ⟨fun h => h.persistent, fun h => ⟨h⟩⟩)
    (all_imp (fun P h => @persistently_elim _ _ P h) hA) hP

end Lfp

section Gfp
open CoMonotoneFixpoint
variable (PROP : Type _) [BI PROP] {Pred : Type _} [CCPO Pred] [PointwiseLifting PROP Pred]
  [PointwiseLiftingLe PROP Pred]
  {F : Pred → Pred} (hF : monotone F)
include hF

theorem gfp_absorbing
    (h : all (B := PROP) Absorbing (F (map (fun P : PROP => iprop(<absorb> P)) (fix F hF)))) :
    all (B := PROP) Absorbing (fix F hF) :=
  fix_all hF (fun _ _ => absorbingly_mono) (fun _ => ⟨fun h => h.absorbing, fun h => ⟨h⟩⟩)
    (all_forall (fun _ => absorbingly_intro) _) h

end Gfp

end IOrder

end Iris
