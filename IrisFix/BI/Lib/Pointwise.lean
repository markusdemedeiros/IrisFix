/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import IrisFix.BI.Lib.Lattice
import all Init.Internal.Order.Basic

/-! # Pointwise Iris fixpoints

`IOrder PROP X` internalizes the CCPO `X` into the BI `PROP`: `a ⊑ᵢ b` is its order, inside the
BI, `meet` its binary meet, `map` applies an operator on `PROP` at every point, and sups respect
`≡{n}≡` and `ne n` (`≡{n}≡`, at arguments `≡{n}≡` in the parameters that have OFEs). `PROP` is
an instance for `-∗` and `∧` (`MonotoneFixpoint`), and for the reverse `-∗` and `∨`
(`CoMonotoneFixpoint`), and functions are instances pointwise. A law for the least fixpoint, in the reverse order, is the law
for the greatest fixpoint. -/

@[expose] public section

namespace Iris
open BI Lean.Order

local bi PROP

/-- `X` has points in `PROP`, and `all C a` says that `C` holds at every point of `a`. -/
class IPoints (PROP : Type _) [BI PROP] (X : Type _) [COFE X] where
  all : (PROP → Prop) → X → Prop
  all_imp {C D : PROP → Prop} (h : ∀ P, C P → D P) {a : X} : all C a → all D a
  all_and {C D : PROP → Prop} {a : X} : all C a → all D a → all (fun P => C P ∧ D P) a
  all_forall {C : PROP → Prop} (h : ∀ P, C P) (a : X) : all C a
  all_lim {C : PROP → Prop} : LimitPreserving C → LimitPreserving (all C)
  /-- The constant `c`, at every point. -/
  const : PROP → X
  all_const {C : PROP → Prop} {c : PROP} : C c → all C (const c)

namespace IPoints
variable {PROP : Type _} [BI PROP]

instance instProp : IPoints PROP PROP where
  all C P := C P
  all_imp h := h _
  all_and := And.intro
  all_forall h P := h P
  all_lim h := h
  const c := c
  all_const h := h

instance instPi {α : Type _} {β : α → Type _} [∀ x, COFE (β x)] [∀ x, IPoints PROP (β x)] :
    IPoints PROP (∀ x, β x) where
  all C f := ∀ x, all C (f x)
  all_imp h := fun hf x => all_imp h (hf x)
  all_and hC hD x := all_and (hC x) (hD x)
  all_forall h f x := all_forall h (f x)
  all_lim h := ⟨fun c hc x => (all_lim h).compl (c.map (OFE.applyHom x)) fun n => hc n x⟩
  const c _ := const c
  all_const h _ := all_const h

end IPoints

open IPoints

/-- `X` internalized into `PROP`: `le` is the order of `X`, inside the BI, `meet` its binary meet,
`map` applies an operator at every point, and sups respect `≡{n}≡` and `ne n`. -/
class IOrder (PROP : Type _) [BI PROP] [CCPO PROP] (X : Type _) [CCPO X] [COFE X]
    extends IPoints PROP X where
  le : X → X → PROP
  meet : X → X → X
  map : (PROP → PROP) → X → X
  ne : Nat → X → X → Prop
  rel_iff {a b : X} : a ⊑ b ↔ ⊢ le a b
  trans {a b c : X} : ⊢ le a b -∗ le b c -∗ le a c
  csup_le {c : X → Prop} (hc : chain c) {R : PROP} {g : X} :
    (∀ f, c f → R ⊢ le f g) → R ⊢ le (CCPO.csup hc) g
  meet_l {a b : X} : meet a b ⊑ a
  meet_r {a b : X} : meet a b ⊑ b
  meet_intro {a b c : X} : ⊢ le a b ∧ le a c -∗ le a (meet b c)
  map_mono {m : PROP → PROP} (hm : ∀ {P Q : PROP}, (P ⊢ Q) → m P ⊢ m Q) : monotone (map m)
  dist_csup {n : Nat} {c₁ c₂ : X → Prop} (hc₁ : chain c₁) (hc₂ : chain c₂) :
    liftRel (· ≡{n}≡ ·) c₁ c₂ → CCPO.csup hc₁ ≡{n}≡ CCPO.csup hc₂
  ne_csup {n : Nat} {c₁ c₂ : X → Prop} (hc₁ : chain c₁) (hc₂ : chain c₂) :
    liftRel (ne n) c₁ c₂ → ne n (CCPO.csup hc₁) (CCPO.csup hc₂)
  all_le {C : PROP → Prop} {m : PROP → PROP} (h : ∀ P, C P ↔ P ⊑ m P) (a : X) :
    all C a ↔ a ⊑ map m a
  all_ge {C : PROP → Prop} {m : PROP → PROP} (h : ∀ P, C P ↔ m P ⊑ P) (a : X) :
    all C a ↔ map m a ⊑ a
  map_const {c : PROP} {a b : X} : map (fun _ => c) a = map (fun _ => c) b

/-- The order of `X`, inside the BI `bi%`. -/
macro:50 a:term:51 " ⊑ᵢ " b:term:51 : term => ``(IOrder.le (PROP := bi%) $a $b)

/-- The binary meet of `X`, for the BI `bi%`. -/
macro:69 a:term:70 " ⊓ᵢ " b:term:70 : term => ``(IOrder.meet (PROP := bi%) $a $b)

/-- Related sets of functions have related sets of values at each point. -/
theorem liftRel_apply {α : Sort _} {β : α → Sort _} {R : ∀ x, β x → β x → Prop}
    {c₁ c₂ : (∀ x, β x) → Prop} (h : liftRel (fun f g => ∀ x, R x (f x) (g x)) c₁ c₂) (x : α) :
    liftRel (R x) (fun v => ∃ f, c₁ f ∧ f x = v) (fun v => ∃ g, c₂ g ∧ g x = v) := by
  refine ⟨fun v ⟨f, hf, hv⟩ => ?_, fun v ⟨g, hg, hv⟩ => ?_⟩
  · obtain ⟨g, hg, hfg⟩ := h.1 f hf
    exact ⟨g x, ⟨g, hg, rfl⟩, hv ▸ hfg x⟩
  · obtain ⟨f, hf, hfg⟩ := h.2 g hg
    exact ⟨f x, ⟨f, hf, rfl⟩, hv ▸ hfg x⟩

namespace IOrder
variable {PROP : Type _} [BI PROP] [CCPO PROP]

/-- An argument without an OFE: `ne` at every point. -/
instance instPi {α : Type _} {β : α → Type _} [∀ x, CCPO (β x)] [∀ x, COFE (β x)]
    [h : ∀ x, IOrder PROP (β x)] : IOrder PROP (∀ x, β x) where
  le f g := iprop(∀ x, f x ⊑ᵢ g x)
  meet f g x := f x ⊓ᵢ g x
  map m f x := map m (f x)
  ne n f g := ∀ x, ne (PROP := PROP) n (f x) (g x)
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
  meet_l x := meet_l
  meet_r x := meet_r
  meet_intro := by
    intro f g k
    iintro H %x
    iapply meet_intro
    isplit
    · icases H with ⟨H, -⟩; iapply H
    · icases H with ⟨-, H⟩; iapply H
  map_mono hm f g hfg x := map_mono hm (f x) (g x) (hfg x)
  dist_csup hc₁ hc₂ hc x := by
    rw [← fun_csup_eq, ← fun_csup_eq]
    exact dist_csup PROP _ _ (liftRel_apply hc x)
  ne_csup hc₁ hc₂ hc x := by
    rw [← fun_csup_eq, ← fun_csup_eq]
    exact ne_csup (PROP := PROP) _ _ (liftRel_apply hc x)
  toIPoints := inferInstance
  all_le h f := forall_congr' fun x => all_le h (f x)
  all_ge h f := forall_congr' fun x => all_ge h (f x)
  map_const := funext fun _ => map_const

/-- An argument with an OFE: `ne n` at `≡{n}≡` arguments. -/
instance (priority := high) instPiNE {α β : Type _} [OFE α] [CCPO β] [COFE β] [IOrder PROP β] :
    IOrder PROP (α → β) :=
  { instPi (β := fun _ => β) with
    ne n f g := ∀ x y, x ≡{n}≡ y → ne (PROP := PROP) n (f x) (g y)
    ne_csup hc₁ hc₂ hc x y hxy := by
      rw [← fun_csup_eq, ← fun_csup_eq]
      -- The values at `x` and at `y` match up, function by function.
      refine ne_csup (PROP := PROP) _ _ ⟨fun v ⟨f, hf, hv⟩ => ?_, fun v ⟨g, hg, hv⟩ => ?_⟩
      · obtain ⟨g, hg, hfg⟩ := hc.1 f hf
        exact ⟨g y, ⟨g, hg, rfl⟩, hv ▸ hfg x y hxy⟩
      · obtain ⟨f, hf, hfg⟩ := hc.2 g hg
        exact ⟨f x, ⟨f, hf, rfl⟩, hv ▸ hfg x y hxy⟩ }

end IOrder

open IOrder

namespace MonotoneFixpoint
variable {PROP : Type _} [BI PROP]

scoped instance instIOrderMonoProp : IOrder PROP PROP where
  le P Q := iprop(P -∗ Q)
  meet P Q := iprop(P ∧ Q)
  map m := m
  ne n P Q := P ≡{n}≡ Q
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
  map_mono hm _ _ := hm
  dist_csup hc₁ hc₂ h := by
    rw [is_sup_unique (CCPO.csup_spec hc₁) (sExists_is_sup _),
      is_sup_unique (CCPO.csup_spec hc₂) (sExists_is_sup _)]
    exact sExists_ne h
  ne_csup hc₁ hc₂ h := by
    rw [is_sup_unique (CCPO.csup_spec hc₁) (sExists_is_sup _),
      is_sup_unique (CCPO.csup_spec hc₂) (sExists_is_sup _)]
    exact sExists_ne h
  toIPoints := inferInstance
  all_le h P := h P
  all_ge h P := h P
  map_const := rfl

end MonotoneFixpoint

namespace CoMonotoneFixpoint
variable {PROP : Type _} [BI PROP]

scoped instance instIOrderAntiProp : IOrder PROP PROP where
  le P Q := iprop(Q -∗ P)
  meet P Q := iprop(P ∨ Q)
  map m := m
  ne n P Q := P ≡{n}≡ Q
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
  map_mono hm _ _ := hm
  dist_csup hc₁ hc₂ h := by
    rw [is_sup_unique (CCPO.csup_spec hc₁) (sForall_is_sup _),
      is_sup_unique (CCPO.csup_spec hc₂) (sForall_is_sup _)]
    exact sForall_ne h
  ne_csup hc₁ hc₂ h := by
    rw [is_sup_unique (CCPO.csup_spec hc₁) (sForall_is_sup _),
      is_sup_unique (CCPO.csup_spec hc₂) (sForall_is_sup _)]
    exact sForall_ne h
  toIPoints := inferInstance
  all_le h P := h P
  all_ge h P := h P
  map_const := rfl

end CoMonotoneFixpoint

namespace IOrder

section Laws
variable {PROP : Type _} [BI PROP] [CCPO PROP] {X : Type _} [CCPO X] [COFE X] [IOrder PROP X]

/-- `F` is monotone inside the BI. -/
def IMono (PROP : Type _) [BI PROP] [CCPO PROP] [IOrder PROP X] (F : X → X) : Prop :=
  ∀ Φ Ψ : X, ⊢ □ (Φ ⊑ᵢ Ψ) -∗ F Φ ⊑ᵢ F Ψ

variable {F : X → X}

theorem monotone_of_imono (hF : IMono PROP F) : monotone F := fun Φ Ψ hΦΨ =>
    (rel_iff (PROP := PROP)).2 <| by
  iapply hF Φ Ψ
  iintro !>
  iapply rel_iff.1 hΦΨ

/-- Iris induction, in the order `⊑ᵢ`. -/
theorem fix_iter (hF : IMono PROP F) (Φ : X) :
    ⊢ □ (F Φ ⊑ᵢ Φ) -∗ fix F (monotone_of_imono hF) ⊑ᵢ Φ :=
  entails_wand <| fix_induct _ (fun f => iprop(□ (F Φ ⊑ᵢ Φ)) ⊢ f ⊑ᵢ Φ)
    (fun _ hc => csup_le hc) fun f ih => by
  iintro #H
  iapply trans (b := F Φ) $$ [] H
  iapply hF f Φ
  iintro !>
  iapply ih $$ H

/-- The fixpoint is below every prefixpoint `g` of a larger body `G`. -/
theorem fix_strong_mono (hF : IMono PROP F) (G : X → X) (g : X) (hg : G g ⊑ g) :
    ⊢ □ (∀ Φ, F Φ ⊑ᵢ G Φ) -∗ fix F (monotone_of_imono hF) ⊑ᵢ g := by
  iintro #H
  iapply fix_iter hF
  iintro !>
  iapply trans (b := G g) $$ [] []
  · iapply H
  · iapply rel_iff.1 hg

/-- Strong induction: the hypothesis also gets the fixpoint, through `meet`. -/
theorem fix_ind (hF : IMono PROP F) (Φ : X) :
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
theorem fix_ind_wf (hF : IMono PROP F) (Φ W : X) (hW : Φ ⊓ᵢ F W ⊑ W) :
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

/-- The fixpoint is `ne` if `F` preserves `ne`. -/
theorem fix_ne (hF : monotone F)
    (hne : ∀ f : X, (∀ n, ne PROP n f f) → ∀ n, ne PROP n (F f) (F f)) :
    ∀ n, ne PROP n (fix F hF) (fix F hF) :=
  fix_induct hF (fun f => ∀ n, ne PROP n f f) (fun _ hc hall n => ne_csup hc hc
    ⟨fun f hf => ⟨f, hf, hall f hf n⟩, fun f hf => ⟨f, hf, hall f hf n⟩⟩) hne

/-- Non-expansive in the body, if `F₂` is non-expansive. `PROP` is explicit: the statement does
not mention it. -/
theorem fix_dist (PROP : Type _) [BI PROP] [CCPO PROP] [IOrder PROP X] {F₁ F₂ : X → X}
    (h₁ : monotone F₁)
    (h₂ : monotone F₂) {n : Nat} (hF₂ : ∀ Φ Ψ, Φ ≡{n}≡ Ψ → F₂ Φ ≡{n}≡ F₂ Ψ)
    (hF : ∀ Φ, F₁ Φ ≡{n}≡ F₂ Φ) : fix F₁ h₁ ≡{n}≡ fix F₂ h₂ := by
  have hFG : monotone fun p : X ×' X => (⟨F₁ p.1, F₂ p.2⟩ : X ×' X) :=
    fun p q hpq => ⟨h₁ _ _ hpq.1, h₂ _ _ hpq.2⟩
  -- Induct on the fixpoint of the pair.
  have hpair := fix_pprod h₁ h₂ hFG
  rw [show fix F₁ h₁ = (fix _ hFG).1 by rw [hpair], show fix F₂ h₂ = (fix _ hFG).2 by rw [hpair]]
  refine fix_induct hFG (fun q => q.1 ≡{n}≡ q.2) (fun c hc hall => ?_)
    fun q hq => (hF q.1).trans (hF₂ _ _ hq)
  rw [← prod_csup_eq]
  exact dist_csup PROP (PProd.chain.chain_fst hc) (PProd.chain.chain_snd hc)
    ⟨fun a ⟨b, hab⟩ => ⟨b, ⟨a, hab⟩, hall _ hab⟩, fun b ⟨a, hab⟩ => ⟨a, ⟨b, hab⟩, hall _ hab⟩⟩

end Laws

/-! ## Instances

An instance at every point is `fix F ⊑ E` for a constant `E`, or `fix F ⊑ m (fix F)` for `m` a
`map` of an operator, which is monotone by `IOrder.map_mono`. -/

section Instances
variable {X : Sort _} [CCPO X] {F : X → X} (hF : monotone F)

/-- Park induction: the fixpoint is below every prefixpoint. -/
theorem fix_le_of {E : X} (hE : F E ⊑ E) : fix F hF ⊑ E :=
  fix_induct hF (· ⊑ E) (fun _ => Lean.Order.csup_le) fun _ h =>
    PartialOrder.rel_trans (hF _ _ h) hE

/-- The fixpoint is below `m` of itself, for a monotone `m` below the identity at the fixpoint,
if `F (m (fix F))` is below `m` of itself. -/
theorem fix_le_map {m : X → X} (hm : monotone m) (hle : m (fix F hF) ⊑ fix F hF)
    (h : F (m (fix F hF)) ⊑ m (F (m (fix F hF)))) : fix F hF ⊑ m (fix F hF) :=
  fix_le_of hF <| PartialOrder.rel_trans h <| hm _ _ <|
    PartialOrder.rel_trans (hF _ _ hle) (PartialOrder.rel_of_eq (fix_eq hF).symm)

end Instances

theorem true_wand_elim {PROP : Type _} [BI PROP] (P : PROP) : iprop(True -∗ P) ⊢ P := by
  iintro H
  iapply H
  ipureintro
  trivial

theorem absorbing_true_wand {PROP : Type _} [BI PROP] (P : PROP) [Absorbing P] :
    P ⊢ iprop(True -∗ P) := by
  iintro H -
  iexact H

/-- `fix_le_map` at `map m`, for an operator `m` on `PROP` that preserves `⊢`. -/
theorem fix_le_imap {PROP : Type _} [BI PROP] [CCPO PROP] {X : Type _} [CCPO X] [COFE X]
    [IOrder PROP X]
    {F : X → X} (hF : monotone F) {m : PROP → PROP} (hm : ∀ {P Q : PROP}, (P ⊢ Q) → m P ⊢ m Q)
    (hle : map m (fix F hF) ⊑ fix F hF)
    (h : F (map m (fix F hF)) ⊑ map m (F (map m (fix F hF)))) : fix F hF ⊑ map m (fix F hF) :=
  fix_le_map hF (map_mono hm) hle h

/-! ### The instances, at every point -/

section All
variable {PROP : Type _} [BI PROP] [CCPO PROP] {X : Type _} [CCPO X] [COFE X] [IOrder PROP X]
  {F : X → X} (hF : monotone F)
include hF

/-- `C` at every point of the fixpoint, for `C P ↔ P ⊑ m P` and `m` below the identity there. -/
theorem fix_all {C : PROP → Prop} {m : PROP → PROP} (hm : ∀ {P Q : PROP}, (P ⊢ Q) → m P ⊢ m Q)
    (hC : ∀ P, C P ↔ P ⊑ m P) (hle : all (fun P => m P ⊑ P) (fix F hF))
    (h : all C (F (map m (fix F hF)))) : all C (fix F hF) :=
  (all_le hC _).2 <| fix_le_imap hF hm ((all_ge (fun _ => .rfl) _).1 hle) ((all_le hC _).1 h)

end All

section Lfp
open MonotoneFixpoint
variable {PROP : Type _} [BI PROP] {X : Type _} [CCPO X] [COFE X] [IOrder PROP X]
  {F : X → X} (hF : monotone F)
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
  fix_all hF wand_mono_right
    (fun P => ⟨fun _ => absorbing_true_wand P, fun h => ⟨sep_symm.trans (wand_elim h)⟩⟩)
    (all_forall true_wand_elim _) h

theorem lfp_persistent_affine
    (hA : all (PROP := PROP) Affine (F (map (fun P : PROP => iprop(□ P)) (fix F hF))))
    (hP : all (PROP := PROP) Persistent (F (map (fun P : PROP => iprop(□ P)) (fix F hF)))) :
    all (PROP := PROP) Persistent (fix F hF) :=
  all_imp (fun _ h => h.2) <| fix_all hF (C := fun P => Affine P ∧ Persistent P)
    intuitionistically_mono
    (fun P => ⟨fun ⟨hA, hP⟩ => (@intuitionistically_of_intuitionistic _ _ P hA hP).2,
      fun h => ⟨⟨h.trans Affine.affine⟩, ⟨h.trans persistently_of_intuitionistically⟩⟩⟩)
    (all_forall (fun _ => intuitionistically_elim) _) (all_and hA hP)

theorem lfp_persistent_absorbing (hA : all (PROP := PROP) Absorbing (fix F hF))
    (hP : all (PROP := PROP) Persistent (F (map (fun P : PROP => iprop(<pers> P)) (fix F hF)))) :
    all (PROP := PROP) Persistent (fix F hF) :=
  fix_all hF persistently_mono (fun _ => ⟨fun h => h.persistent, fun h => ⟨h⟩⟩)
    (all_imp (fun P h => @persistently_elim _ _ P h) hA) hP

end Lfp

section Gfp
open CoMonotoneFixpoint
variable {PROP : Type _} [BI PROP] {X : Type _} [CCPO X] [COFE X] [IOrder PROP X]
  {F : X → X} (hF : monotone F)
include hF

theorem gfp_absorbing
    (h : all (PROP := PROP) Absorbing (F (map (fun P : PROP => iprop(<absorb> P)) (fix F hF)))) :
    all (PROP := PROP) Absorbing (fix F hF) :=
  fix_all hF absorbingly_mono (fun _ => ⟨fun h => h.absorbing, fun h => ⟨h⟩⟩)
    (all_forall (fun _ => absorbingly_intro) _) h

end Gfp

end IOrder

end Iris
