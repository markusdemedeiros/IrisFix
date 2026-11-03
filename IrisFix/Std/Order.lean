/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.Init
import all Init.Internal.Order.Basic

/-! # Order theory for `partial_fixpoint`

Facts about `Lean.Order` CCPOs and their fixpoints. -/

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

end Order

end Iris
