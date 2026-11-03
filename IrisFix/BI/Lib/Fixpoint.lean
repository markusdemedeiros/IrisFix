/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import IrisFix.BI.Lib.Monotone
public import IrisFix.Std.Order
import all Init.Internal.Order.Basic

/-! # Iris fixpoints

`partial_fixpoint` takes fixpoints in a CCPO `Pred`. Here `Pred` is a family of propositions
(`PROP`, `A → PROP`, …), and each class below lifts one notion from `PROP` to `Pred`, a point at a
time:

* `IPoints PROP Pred`: `all C a`, the property `C` at every point of `a`.
* `IPointsLim PROP Pred`: `all` survives limits, and constant families. For the Banach laws.
* `IOrder PROP Pred`: `a ⊑ᵢ b`, the order of `Pred`, inside the BI. For induction.
* `IMeet PROP Pred`: `a ⊓ᵢ b`, the binary meet of `Pred`. For strong induction.
* `IMap PROP Pred`: `map m a`, an operator `m` on `PROP` at every point. For the instances.
* `INe Pred` (in `IrisFix.Std.Order`): `ne n`, agreement up to `n`, jointly in the arguments that
  have OFEs.

Entailment (`MonotoneFixpoint`) and reverse entailment (`CoMonotoneFixpoint`) make `PROP` a CCPO,
so `partial_fixpoint` defines least and greatest fixpoints. `PROP` is an instance of every class,
for `-∗` and `∧` (`MonotoneFixpoint`) and for the reverse `-∗` and `∨` (`CoMonotoneFixpoint`), and
functions are instances pointwise. A law for the least fixpoint, in the reverse order, is the law
for the greatest fixpoint. All the operations unfold, at concrete instances, to the plain curried
statements. -/

@[expose] public section

namespace Iris
open BI Lean.Order

local bi PROP

/-! ## Embedding classes
The classes in this section represent different ways that `PROP` lifts to `Pred`.
The canonical example to keep in mind is families of propositions `Pred := A → PROP`: the classes
here outline how different aspects of `PROP` may lift to families of propositions.-/

/-- Properties of propositions lift to `Pred`: `all C a` says `C` holds at every proposition in `a`.
For example, with `Pred := A → PROP`, one could define `all C F := ∀ a : A, C (F a)`. -/
class IPoints (PROP : Type _) [BI PROP] (Pred : Type _) where
  all : (PROP → Prop) → Pred → Prop
  all_imp {C D : PROP → Prop} (h : ∀ P, C P → D P) {a : Pred} : all C a → all D a
  all_and {C D : PROP → Prop} {a : Pred} : all C a → all D a → all (fun P => C P ∧ D P) a
  all_forall {C : PROP → Prop} (h : ∀ P, C P) (a : Pred) : all C a

open IPoints

/-- `all` preserves limits, and every proposition `c` lifts to the constant family `const c`.
For example, with `Pred := A → PROP`, `const c := fun _ => c`. -/
class IPointsLim (PROP : Type _) [BI PROP] (Pred : Type _) [COFE Pred] [IPoints PROP Pred] where
  all_lim {C : PROP → Prop} : LimitPreserving C → LimitPreserving (all C : Pred → Prop)
  const : PROP → Pred
  all_const {C : PROP → Prop} {c : PROP} : C c → all C (const c)

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

/-- Functions on `PROP` lift to functions on `Pred`.
For example, with `Pred := A → PROP`, one can lift maps `f : PROP → PROP` into maps on
`fun (x : A → PROP) (a : A) => f (x a)`. This class requires the lifting on maps to be compatible
with universal quantification. -/
class IMap (PROP : Type _) [BI PROP] [PartialOrder PROP] (Pred : Type _) [PartialOrder Pred]
    [IPoints PROP Pred] where
  map : (PROP → PROP) → Pred → Pred
  map_mono {m : PROP → PROP} (hm : monotone m) : monotone (map m)
  all_le {C : PROP → Prop} {m : PROP → PROP} (h : ∀ P, C P ↔ P ⊑ m P) (a : Pred) :
    all C a ↔ a ⊑ map m a
  map_le {m : PROP → PROP} {a : Pred} : all (fun P => m P ⊑ P) a → map m a ⊑ a
  map_const {c : PROP} {a b : Pred} : map (fun _ => c) a = map (fun _ => c) b

open IPointsLim IOrder IMeet IMap INe

/-! ## Functions, pointwise -/

section Pi
variable {PROP : Type _} [BI PROP] {ι : Type _} {β : ι → Type _}

instance IPoints.instProp : IPoints PROP PROP where
  all C P := C P
  all_imp h := h _
  all_and := And.intro
  all_forall h P := h P

instance IPoints.instPi [∀ x, IPoints PROP (β x)] : IPoints PROP (∀ x, β x) where
  all C f := ∀ x, all C (f x)
  all_imp h := fun hf x => all_imp h (hf x)
  all_and hC hD x := all_and (hC x) (hD x)
  all_forall h f x := all_forall h (f x)

instance IPointsLim.instProp : IPointsLim PROP PROP where
  all_lim h := h
  const c := c
  all_const h := h

instance IPointsLim.instPi [∀ x, COFE (β x)] [∀ x, IPoints PROP (β x)]
    [∀ x, IPointsLim PROP (β x)] : IPointsLim PROP (∀ x, β x) where
  all_lim h := ⟨fun c hc x => (all_lim h).compl (c.map (OFE.applyHom x)) fun n => hc n x⟩
  const c _ := const c
  all_const h _ := all_const h

instance IOrder.instPi [∀ x, CCPO (β x)] [∀ x, IOrder PROP (β x)] : IOrder PROP (∀ x, β x) where
  le f g := iprop(∀ x, f x ⊑ᵢ g x)
  rel_iff := ⟨fun hfg => forall_intro fun x => rel_iff.1 (hfg x),
    fun hfg x => rel_iff.2 (hfg.trans (forall_elim x))⟩
  trans := by
    intro f g k
    iintro Hfg Hgk %x
    iapply trans $$ [Hfg] [Hgk]
    · iapply Hfg
    · iapply Hgk
  csup_le hc := fun hall => forall_intro fun x => by
    rw [← fun_csup_eq]
    exact csup_le _ fun v ⟨f, hf, hv⟩ => hv ▸ (hall f hf).trans (forall_elim x)

instance IMeet.instPi [∀ x, CCPO (β x)] [∀ x, IOrder PROP (β x)] [∀ x, IMeet PROP (β x)] :
    IMeet PROP (∀ x, β x) where
  meet f g x := f x ⊓ᵢ g x
  meet_l x := meet_l
  meet_r x := meet_r
  meet_intro := by
    intro f g k
    dsimp only [IOrder.le]
    iintro H %x
    iapply meet_intro
    isplit
    · icases H with ⟨H, -⟩; iapply H
    · icases H with ⟨-, H⟩; iapply H

instance IMap.instPi [PartialOrder PROP] [∀ x, PartialOrder (β x)] [∀ x, IPoints PROP (β x)]
    [∀ x, IMap PROP (β x)] : IMap PROP (∀ x, β x) where
  map m f x := map m (f x)
  map_mono hm f g hfg x := map_mono hm (f x) (g x) (hfg x)
  all_le h f := forall_congr' fun x => all_le h (f x)
  map_le h x := map_le (h x)
  map_const := funext fun _ => map_const

/-- `PROP` itself, in either order. -/
instance IMap.instProp [PartialOrder PROP] : IMap PROP PROP where
  map m := m
  map_mono hm := hm
  all_le h P := h P
  map_le h := h
  map_const := rfl

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
`map` of an operator, which is monotone by `IMap.map_mono`: Park induction (`fix_le_of`,
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

section All
variable {PROP : Type _} [BI PROP] [PartialOrder PROP] {Pred : Type _} [CCPO Pred]
  [IPoints PROP Pred] [IMap PROP Pred] {F : Pred → Pred} (hF : monotone F)
include hF

/-- `C` at every point of the fixpoint, for `C P ↔ P ⊑ m P` and `m` below the identity there. -/
theorem fix_all {C : PROP → Prop} {m : PROP → PROP} (hm : monotone m)
    (hC : ∀ P, C P ↔ P ⊑ m P) (hle : all (fun P => m P ⊑ P) (fix F hF))
    (h : all C (F (map m (fix F hF)))) : all C (fix F hF) :=
  (all_le hC _).2 <| fix_le_map hF (map_mono hm) (map_le hle) ((all_le hC _).1 h)

end All

section Lfp
open MonotoneFixpoint
variable {PROP : Type _} [BI PROP] {Pred : Type _} [CCPO Pred] [IPoints PROP Pred] [IMap PROP Pred]
  {F : Pred → Pred} (hF : monotone F)
include hF

theorem lfp_affine
    (h : all (PROP := PROP) Affine (F (map (fun _ : PROP => iprop(emp)) (fix F hF)))) :
    all (PROP := PROP) Affine (fix F hF) := by
  have hC (P : PROP) : Affine P ↔ P ⊑ (fun _ => iprop(emp)) P := ⟨fun h => h.affine, fun h => ⟨h⟩⟩
  -- Park induction at the constant `emp`.
  exact (all_le hC _).2 <| fix_le_of hF <|
    PartialOrder.rel_trans ((all_le hC _).1 h) (PartialOrder.rel_of_eq map_const)

theorem lfp_absorbing
    (h : all (PROP := PROP) Absorbing (F (map (fun P : PROP => iprop(True -∗ P)) (fix F hF)))) :
    all (PROP := PROP) Absorbing (fix F hF) :=
  fix_all hF (fun _ _ => wand_mono_right)
    (fun P => ⟨fun _ => absorbing_true_wand P, fun h => ⟨sep_symm.trans (wand_elim h)⟩⟩)
    (all_forall true_wand_elim _) h

theorem lfp_persistent_affine
    (hA : all (PROP := PROP) Affine (F (map (fun P : PROP => iprop(□ P)) (fix F hF))))
    (hP : all (PROP := PROP) Persistent (F (map (fun P : PROP => iprop(□ P)) (fix F hF)))) :
    all (PROP := PROP) Persistent (fix F hF) :=
  all_imp (fun _ h => h.2) <| fix_all hF (C := fun P => Affine P ∧ Persistent P)
    (fun _ _ => intuitionistically_mono)
    (fun P => ⟨fun ⟨hA, hP⟩ => (@intuitionistically_of_intuitionistic _ _ P hA hP).2,
      fun h => ⟨⟨h.trans Affine.affine⟩, ⟨h.trans persistently_of_intuitionistically⟩⟩⟩)
    (all_forall (fun _ => intuitionistically_elim) _) (all_and hA hP)

theorem lfp_persistent_absorbing (hA : all (PROP := PROP) Absorbing (fix F hF))
    (hP : all (PROP := PROP) Persistent (F (map (fun P : PROP => iprop(<pers> P)) (fix F hF)))) :
    all (PROP := PROP) Persistent (fix F hF) :=
  fix_all hF (fun _ _ => persistently_mono) (fun _ => ⟨fun h => h.persistent, fun h => ⟨h⟩⟩)
    (all_imp (fun P h => @persistently_elim _ _ P h) hA) hP

end Lfp

section Gfp
open CoMonotoneFixpoint
variable {PROP : Type _} [BI PROP] {Pred : Type _} [CCPO Pred] [IPoints PROP Pred] [IMap PROP Pred]
  {F : Pred → Pred} (hF : monotone F)
include hF

theorem gfp_absorbing
    (h : all (PROP := PROP) Absorbing (F (map (fun P : PROP => iprop(<absorb> P)) (fix F hF)))) :
    all (PROP := PROP) Absorbing (fix F hF) :=
  fix_all hF (fun _ _ => absorbingly_mono) (fun _ => ⟨fun h => h.absorbing, fun h => ⟨h⟩⟩)
    (all_forall (fun _ => absorbingly_intro) _) h

end Gfp

end IOrder

end Iris
