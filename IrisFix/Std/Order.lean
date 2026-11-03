/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.Init
public import Iris.BI.BI
import all Init.Internal.Order.Basic

/-! # Order theory for `partial_fixpoint`

Facts about `Lean.Order` CCPOs and their fixpoints, and `INe`: an indexed relation that sups
preserve, such as non-expansiveness. -/

@[expose] public section

namespace Iris
open Lean.Order

section Order
variable {α β : Sort _}

/-- The fixpoint of a pair of functions is the pair of their fixpoints. -/
theorem fix_pprod [CCPO α] [CCPO β] {F : α → α} {G : β → β} (hF : monotone F) (hG : monotone G)
    (hFG : monotone fun p : α ×' β => (⟨F p.1, G p.2⟩ : α ×' β)) :
    fix _ hFG = ⟨fix F hF, fix G hG⟩ := by
  refine PartialOrder.rel_antisymm ?_ (show _ ∧ _ from ⟨?_, ?_⟩)
  · refine fix_induct hFG (· ⊑ ⟨fix F hF, fix G hG⟩) (fun _ => csup_le) fun q hq => ?_
    rw [fix_eq hF, fix_eq hG]
    exact ⟨hF _ _ hq.1, hG _ _ hq.2⟩
  · exact fix_induct hF (· ⊑ (fix _ hFG).1) (fun _ => csup_le) fun f hf => by
      rw [fix_eq hFG]; exact hF _ _ hf
  · exact fix_induct hG (· ⊑ (fix _ hFG).2) (fun _ => csup_le) fun g hg => by
      rw [fix_eq hFG]; exact hG _ _ hg

/-- Fixpoints of related bodies are related, for a relation `R` that sups of related chains
preserve. -/
theorem fix_rel [CCPO α] {F₁ F₂ : α → α} (h₁ : monotone F₁) (h₂ : monotone F₂)
    {R : α → α → Prop}
    (hR : ∀ {c₁ c₂ : α → Prop} (hc₁ : chain c₁) (hc₂ : chain c₂),
      liftRel R c₁ c₂ → R (CCPO.csup hc₁) (CCPO.csup hc₂))
    (hF : ∀ f g, R f g → R (F₁ f) (F₂ g)) : R (fix F₁ h₁) (fix F₂ h₂) := by
  have hFG : monotone fun p : α ×' α => (⟨F₁ p.1, F₂ p.2⟩ : α ×' α) :=
    fun p q hpq => ⟨h₁ _ _ hpq.1, h₂ _ _ hpq.2⟩
  -- Induct on the fixpoint of the pair.
  have hpair := fix_pprod h₁ h₂ hFG
  rw [show fix F₁ h₁ = (fix _ hFG).1 by rw [hpair], show fix F₂ h₂ = (fix _ hFG).2 by rw [hpair]]
  refine fix_induct hFG (fun q => R q.1 q.2) (fun c hc hall => ?_) fun q hq => hF _ _ hq
  rw [← prod_csup_eq]
  exact hR (PProd.chain.chain_fst hc) (PProd.chain.chain_snd hc)
    ⟨fun a ⟨b, hab⟩ => ⟨b, ⟨a, hab⟩, hall _ hab⟩, fun b ⟨a, hab⟩ => ⟨a, ⟨b, hab⟩, hall _ hab⟩⟩

end Order

section Park
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

end Park

/-! ## Indexed relations that sups preserve -/

/-- The `CCPO X` has an indexed relation, and supremums preserve it. -/
class INe (X : Type _) [CCPO X] where
  ne : Nat → X → X → Prop
  ne_csup {n : Nat} {c₁ c₂ : X → Prop} (hc₁ : chain c₁) (hc₂ : chain c₂) :
    liftRel (ne n) c₁ c₂ → ne n (CCPO.csup hc₁) (CCPO.csup hc₂)

/-- Related sets of functions have related sets of values at each point. -/
theorem liftRel_apply {α : Sort _} {β : α → Sort _} {R : ∀ x, β x → β x → Prop}
    {c₁ c₂ : (∀ x, β x) → Prop} (h : liftRel (fun f g => ∀ x, R x (f x) (g x)) c₁ c₂) (x : α) :
    liftRel (R x) (fun v => ∃ f, c₁ f ∧ f x = v) (fun v => ∃ g, c₂ g ∧ g x = v) := by
  refine ⟨fun v ⟨f, hf, hv⟩ => ?_, fun v ⟨g, hg, hv⟩ => ?_⟩
  · obtain ⟨g, hg, hfg⟩ := h.1 f hf
    exact ⟨g x, ⟨g, hg, rfl⟩, hv ▸ hfg x⟩
  · obtain ⟨f, hf, hfg⟩ := h.2 g hg
    exact ⟨f x, ⟨f, hf, rfl⟩, hv ▸ hfg x⟩

section Pi
variable {α : Type _} {β : α → Type _}
open INe

/-- An argument without an OFE: `ne` at every point. -/
instance INe.instPi [∀ x, CCPO (β x)] [∀ x, INe (β x)] : INe (∀ x, β x) where
  ne n f g := ∀ x, ne n (f x) (g x)
  ne_csup hc₁ hc₂ hc x := by
    rw [← fun_csup_eq, ← fun_csup_eq]
    exact ne_csup _ _ (liftRel_apply hc x)

/-- An argument with an OFE: `ne n` at `≡{n}≡` arguments. -/
instance (priority := high) INe.instPiNE {α β : Type _} [OFE α] [CCPO β] [INe β] :
    INe (α → β) where
  ne n f g := ∀ x x', x ≡{n}≡ x' → ne n (f x) (g x')
  ne_csup hc₁ hc₂ hc x x' hx := by
    rw [← fun_csup_eq, ← fun_csup_eq]
    -- The values at `x` and at `x'` match up, function by function.
    refine ne_csup _ _ ⟨fun v ⟨f, hf, hv⟩ => ?_, fun v ⟨g, hg, hv⟩ => ?_⟩
    · obtain ⟨g, hg, hfg⟩ := hc.1 f hf
      exact ⟨g x', ⟨g, hg, rfl⟩, hv ▸ hfg x x' hx⟩
    · obtain ⟨f, hf, hfg⟩ := hc.2 g hg
      exact ⟨f x, ⟨f, hf, rfl⟩, hv ▸ hfg x x' hx⟩

end Pi

/-- Fixpoints of bodies that preserve `ne n` are `ne n`. At `F₁ = F₂`, the fixpoint is
non-expansive in the arguments with OFEs; at arguments without, it is non-expansive in the body. -/
theorem fix_ne {X : Type _} [CCPO X] [INe X] {F₁ F₂ : X → X} (h₁ : monotone F₁)
    (h₂ : monotone F₂) {n : Nat} (hF : ∀ f g, INe.ne n f g → INe.ne n (F₁ f) (F₂ g)) :
    INe.ne n (fix F₁ h₁) (fix F₂ h₂) :=
  fix_rel h₁ h₂ INe.ne_csup hF

end Iris
