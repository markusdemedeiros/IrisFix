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
(`PROP`, `A → PROP`, …), a `PointwiseLifting` of `PROP` (`IrisFix.Std.PointwiseLifting`).

Entailment (`MonotoneFixpoint`) and reverse entailment (`CoMonotoneFixpoint`) make `PROP` a CCPO,
so `partial_fixpoint` defines least and greatest fixpoints. `IOrder PROP` is the order of that CCPO
inside the BI, with its binary meet: `-∗` and `∧`, or the reverse `-∗` and `∨`. A law for the least
fixpoint, in the reverse order, is the law for the greatest fixpoint.

Every structure on `Pred` is a structure on `PROP`, at every point: `a ⊑ᵢ b` is `IOrder.le`
lifted by `IPointwiseLifting.irel`, which quantifies with the BI's `∀`; `a ⊓ᵢ b` is `IOrder.meet`
lifted by `zip`; `all C a` is `C` at every point, and `map m a` is `m` at every point. `INe`, agreement
up to `n` in the arguments that have OFEs, lifts by its own `Pi` instances. All of them unfold, at
concrete instances, to the plain curried statements.

The laws hold at any fixpoint `IsFix F fn`, such as a `partial_fixpoint`, by its induction
principle and its unfolding. -/

@[expose] public section

namespace Iris
open BI Lean.Order

local bi PROP

/-! ## Pointwise relations into the BI -/

section Pi
variable {PROP : Type _} [BI PROP] {ι : Type _} {β : ι → Type _}
open PointwiseLifting (rel zip)

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

end Pi

/-! ## The order of `PROP`, inside the BI -/

/-- The order of the CCPO `PROP`, inside the BI, and its binary meet. -/
class IOrder (PROP : Type _) [BI PROP] [CCPO PROP] where
  le : PROP → PROP → PROP
  meet : PROP → PROP → PROP
  rel_iff {P Q : PROP} : P ⊑ Q ↔ ⊢ le P Q
  trans {P Q R : PROP} : ⊢ le P Q -∗ le Q R -∗ le P R
  csup_le {c : PROP → Prop} (hc : chain c) {R Q : PROP} :
    (∀ P, c P → R ⊢ le P Q) → R ⊢ le (CCPO.csup hc) Q
  meet_l {P Q : PROP} : meet P Q ⊑ P
  meet_r {P Q : PROP} : meet P Q ⊑ Q
  meet_intro {P Q R : PROP} : ⊢ le P Q ∧ le P R -∗ le P (meet Q R)

/-- The order of `Pred`, inside the BI `bi%`: `IOrder.le` at every point. -/
macro:50 a:term:51 " ⊑ᵢ " b:term:51 : term =>
  ``(IPointwiseLifting.irel (PROP := bi%) IOrder.le $a $b)

/-- The binary meet of `Pred`, for the BI `bi%`: `IOrder.meet` at every point. -/
macro:69 a:term:70 " ⊓ᵢ " b:term:70 : term =>
  ``(PointwiseLifting.zip (B := bi%) IOrder.meet $a $b)

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

scoped instance instIOrderMonoProp : IOrder PROP where
  le P Q := iprop(P -∗ Q)
  meet P Q := iprop(P ∧ Q)
  rel_iff := ⟨entails_wand, wand_entails⟩
  trans := by
    intro P Q R
    iintro HPQ HQR HP
    iapply HQR
    iapply HPQ $$ HP
  csup_le hc := fun hall => wand_intro <| sep_symm.trans <| wand_elim <|
    ((CCPO.csup_spec hc _).2 fun f hf => wand_intro <| sep_symm.trans <| wand_elim (hall f hf) :)
  meet_l := and_elim_l
  meet_r := and_elim_r
  meet_intro := by
    intro P Q R
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

scoped instance instIOrderAntiProp : IOrder PROP where
  le P Q := iprop(Q -∗ P)
  meet P Q := iprop(P ∨ Q)
  rel_iff := ⟨entails_wand, wand_entails⟩
  trans := by
    intro P Q R
    iintro HQP HRQ HR
    iapply HQP
    iapply HRQ $$ HR
  csup_le hc := fun hall => wand_intro <|
    ((CCPO.csup_spec hc _).2 fun f hf => wand_elim (hall f hf) :)
  meet_l := or_intro_l
  meet_r := or_intro_r
  meet_intro := by
    intro P Q R
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
open PointwiseLifting (rel_mono rel_zip_l rel_zip_r)
open PointwiseLiftingLe (le_iff)
open IPointwiseLifting (irel_valid irel_trans irel_zip irel_csup)

section Laws
variable {PROP : Type _} [BI PROP] [CCPO PROP] [IOrder PROP] {Pred : Type _} [CCPO Pred]
  [PointwiseLifting PROP Pred] [IPointwiseLifting PROP Pred]

variable (PROP) in
/-- `F` is monotone inside the BI. -/
def IMono (F : Pred → Pred) : Prop := ∀ Φ Ψ : Pred, ⊢ □ (Φ ⊑ᵢ Ψ) -∗ F Φ ⊑ᵢ F Ψ

/-! ### `⊑ᵢ` and `⊓ᵢ`, at every point -/

theorem ile_trans {a b c : Pred} : ⊢ a ⊑ᵢ b -∗ b ⊑ᵢ c -∗ a ⊑ᵢ c :=
  irel_trans (R := le) (S := le) (T := le) fun _ _ _ => trans

theorem ile_csup {c : Pred → Prop} (hc : chain c) {R : PROP} {g : Pred} :
    (∀ f, c f → R ⊢ f ⊑ᵢ g) → R ⊢ CCPO.csup hc ⊑ᵢ g :=
  irel_csup (R := le) (fun hc => csup_le hc) hc

theorem imeet_intro {a b c : Pred} : ⊢ a ⊑ᵢ b ∧ a ⊑ᵢ c -∗ a ⊑ᵢ (b ⊓ᵢ c) :=
  irel_zip (R := le) (S := le) (T := le) (f := meet) fun _ _ _ => meet_intro

variable [PointwiseLiftingLe PROP Pred]

theorem ile_iff {a b : Pred} : a ⊑ b ↔ ⊢ a ⊑ᵢ b := by
  rw [le_iff (B := PROP), irel_valid]
  exact ⟨rel_mono fun _ _ => rel_iff.1, rel_mono fun _ _ => rel_iff.2⟩

omit [IPointwiseLifting PROP Pred] in
theorem imeet_l {a b : Pred} : a ⊓ᵢ b ⊑ a :=
  (le_iff (B := PROP)).2 (rel_zip_l (fun _ _ => meet_l) _ _)

omit [IPointwiseLifting PROP Pred] in
theorem imeet_r {a b : Pred} : a ⊓ᵢ b ⊑ b :=
  (le_iff (B := PROP)).2 (rel_zip_r (fun _ _ => meet_r) _ _)

/-! ### Induction -/

variable {F : Pred → Pred}

theorem monotone_of_imono (hF : IMono PROP F) : monotone F := fun Φ Ψ hΦΨ =>
    (ile_iff (PROP := PROP)).2 <| by
  iapply hF Φ Ψ
  iintro !>
  iapply ile_iff.1 hΦΨ

variable {fn : Pred} (hfix : IsFix F fn) (hF : IMono PROP F)
include hfix hF

omit [PointwiseLiftingLe PROP Pred] in
/-- Iris induction, in the order `⊑ᵢ`. -/
theorem _root_.Iris.IsFix.iter (Φ : Pred) : ⊢ □ (F Φ ⊑ᵢ Φ) -∗ fn ⊑ᵢ Φ :=
  entails_wand <| hfix.induct (fun f => iprop(□ (F Φ ⊑ᵢ Φ)) ⊢ f ⊑ᵢ Φ)
    (fun _ hc => ile_csup hc) fun f ih => by
  iintro #H
  iapply ile_trans (b := F Φ) $$ [] H
  iapply hF f Φ
  iintro !>
  iapply ih $$ H

/-- The fixpoint is below every prefixpoint `g` of a larger body `G`. -/
theorem _root_.Iris.IsFix.strong_mono (G : Pred → Pred) (g : Pred) (hg : G g ⊑ g) :
    ⊢ □ (∀ Φ, F Φ ⊑ᵢ G Φ) -∗ fn ⊑ᵢ g := by
  iintro #H
  iapply hfix.iter hF
  iintro !>
  iapply ile_trans (b := G g) $$ [] []
  · iapply H
  · iapply ile_iff.1 hg

/-- Strong induction: the hypothesis also gets the fixpoint, through `⊓ᵢ`. -/
theorem _root_.Iris.IsFix.ind (Φ : Pred) : ⊢ □ (F (Φ ⊓ᵢ fn) ⊑ᵢ Φ) -∗ fn ⊑ᵢ Φ := by
  iintro #H
  iapply ile_trans (b := Φ ⊓ᵢ fn) $$ [] []
  · iapply hfix.iter hF
    iintro !>
    iapply imeet_intro
    isplit
    · iexact H
    -- `Φ ⊓ᵢ fn` is below `fn`, so `F` of it is below `F fn = fn`.
    · iapply ile_trans (b := F fn) $$ [] []
      · iapply hF (Φ ⊓ᵢ fn) fn
        iintro !>
        iapply ile_iff.1 imeet_r
      · iapply ile_iff.1 (PartialOrder.rel_of_eq hfix.unfold.symm)
  · iapply ile_iff.1 imeet_l

/-- Well-founded induction, for `W` above `Φ ⊓ᵢ F W`. In the reverse order, this is
parameterized coinduction. -/
theorem _root_.Iris.IsFix.ind_wf (Φ W : Pred) (hW : Φ ⊓ᵢ F W ⊑ W) :
    ⊢ □ (F W ⊑ᵢ Φ) -∗ fn ⊑ᵢ Φ := by
  iintro #H
  -- `fn = F fn`, which is below `F W` since `fn` is below `W`.
  iapply ile_trans (b := F fn) $$ [] []
  · iapply ile_iff.1 (PartialOrder.rel_of_eq hfix.unfold)
  iapply ile_trans (b := F W) $$ [] H
  iapply hF fn W
  iintro !>
  iapply hfix.iter hF
  iintro !>
  iapply ile_trans (b := Φ ⊓ᵢ F W) $$ [] []
  · iapply imeet_intro
    isplit
    · iexact H
    · iapply ile_iff.1 PartialOrder.rel_refl
  · iapply ile_iff.1 hW

end Laws

/-! ## Instances

An instance at every point is `fn ⊑ E` for a constant `E`, or `fn ⊑ m fn` for `m` a `map` of an
operator, which is monotone by `PointwiseLifting.map_mono`: Park induction (`IsFix.le_of`,
`IsFix.le_map`). -/

private theorem true_wand_elim {PROP : Type _} [BI PROP] (P : PROP) : iprop(True -∗ P) ⊢ P := by
  iintro H
  iapply H
  ipureintro
  trivial

private theorem absorbing_true_wand {PROP : Type _} [BI PROP] (P : PROP) [Absorbing P] :
    P ⊢ iprop(True -∗ P) := by
  iintro H -
  iexact H

open PointwiseLifting (all all_imp all_and all_forall map all_le map_const)

section Lfp
open MonotoneFixpoint
variable (PROP : Type _) [BI PROP] {Pred : Type _} [CCPO Pred] [PointwiseLifting PROP Pred]
  [PointwiseLiftingLe PROP Pred] {F : Pred → Pred} {fn : Pred} (hfix : IsFix F fn)
  (hF : monotone F)
include hfix hF

theorem _root_.Iris.IsFix.lfp_affine
    (h : all (B := PROP) Affine (F (map (fun _ : PROP => iprop(emp)) fn))) :
    all (B := PROP) Affine fn := by
  have hC (P : PROP) : Affine P ↔ P ⊑ (fun _ => iprop(emp)) P := ⟨fun h => h.affine, fun h => ⟨h⟩⟩
  -- Park induction at the constant `emp`.
  exact (all_le hC _).2 <| hfix.le_of hF <|
    PartialOrder.rel_trans ((all_le hC _).1 h) (PartialOrder.rel_of_eq map_const)

theorem _root_.Iris.IsFix.lfp_absorbing
    (h : all (B := PROP) Absorbing (F (map (fun P : PROP => iprop(True -∗ P)) fn))) :
    all (B := PROP) Absorbing fn :=
  hfix.all hF (fun _ _ => wand_mono_right)
    (fun P => ⟨fun _ => absorbing_true_wand P, fun h => ⟨sep_symm.trans (wand_elim h)⟩⟩)
    (all_forall true_wand_elim _) h

theorem _root_.Iris.IsFix.lfp_persistent_affine
    (hA : all (B := PROP) Affine (F (map (fun P : PROP => iprop(□ P)) fn)))
    (hP : all (B := PROP) Persistent (F (map (fun P : PROP => iprop(□ P)) fn))) :
    all (B := PROP) Persistent fn :=
  all_imp (fun _ h => h.2) <| hfix.all hF (C := fun P => Affine P ∧ Persistent P)
    (fun _ _ => intuitionistically_mono)
    (fun P => ⟨fun ⟨hA, hP⟩ => (@intuitionistically_of_intuitionistic _ _ P hA hP).2,
      fun h => ⟨⟨h.trans Affine.affine⟩, ⟨h.trans persistently_of_intuitionistically⟩⟩⟩)
    (all_forall (fun _ => intuitionistically_elim) _) (all_and hA hP)

theorem _root_.Iris.IsFix.lfp_persistent_absorbing (hA : all (B := PROP) Absorbing fn)
    (hP : all (B := PROP) Persistent (F (map (fun P : PROP => iprop(<pers> P)) fn))) :
    all (B := PROP) Persistent fn :=
  hfix.all hF (fun _ _ => persistently_mono) (fun _ => ⟨fun h => h.persistent, fun h => ⟨h⟩⟩)
    (all_imp (fun P h => @persistently_elim _ _ P h) hA) hP

end Lfp

section Gfp
open CoMonotoneFixpoint
variable (PROP : Type _) [BI PROP] {Pred : Type _} [CCPO Pred] [PointwiseLifting PROP Pred]
  [PointwiseLiftingLe PROP Pred] {F : Pred → Pred} {fn : Pred} (hfix : IsFix F fn)
  (hF : monotone F)
include hfix hF

theorem _root_.Iris.IsFix.gfp_absorbing
    (h : all (B := PROP) Absorbing (F (map (fun P : PROP => iprop(<absorb> P)) fn))) :
    all (B := PROP) Absorbing fn :=
  hfix.all hF (fun _ _ => absorbingly_mono) (fun _ => ⟨fun h => h.absorbing, fun h => ⟨h⟩⟩)
    (all_forall (fun _ => absorbingly_intro) _) h

end Gfp

end IOrder

end Iris
