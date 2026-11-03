/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.BI
public import IrisFix.ProofMode.Lib.Guarded

@[expose] public section
open Iris BI OFE

namespace IrisTest.FixpointGuarded

local bi PROP

variable {PROP : Type _} [BI PROP] [BILaterContractive PROP] [Inhabited PROP]

iguarded g2 (b : Bool) (n : Nat) : PROP := iprop(▷ g2 (!b) (n + 1))
contractive_by
  intros k Φ Ψ h b n; unfold g2.pre; exact Contractive.distLater_dist (fun m hm => h m hm _ _)

example (b : Bool) (n : Nat) : g2 (PROP := PROP) b n = g2.pre g2 b n := g2.unfold b n

example : g2 (PROP := PROP) = fixpoint g2.pre := g2.eq_fixpoint

example (b : Bool) (n : Nat) : Persistent (g2 (PROP := PROP) b n) :=
  g2.persistent (fun _ h b n => by unfold g2.pre; have := h (!b) (n + 1); infer_instance) b n


-- A function type: its parameters vary too.
iguarded gf (n : Nat) : Bool → PROP := fun b => iprop(▷ gf (n + 1) b)
contractive_by
  intros k Φ Ψ h n b; unfold gf.pre; exact Contractive.distLater_dist (fun m hm => h m hm _ _)

example (n : Nat) (b : Bool) : gf (PROP := PROP) n b = gf.pre gf n b := gf.unfold n b

-- `wp`-shaped: the last parameter is a predicate.
iguarded wpish (n : Nat) (Φ : Nat → PROP) : PROP := iprop(Φ n ∨ ▷ wpish (n + 1) fun m => Φ (m + 1))
contractive_by
  intros k Ψ₁ Ψ₂ h n Φ; unfold wpish.pre
  exact or_ne.ne .rfl (Contractive.distLater_dist fun m hm => h m hm _ _)

example (n : Nat) (Φ : Nat → PROP) :
    wpish n Φ = iprop(Φ n ∨ ▷ wpish (n + 1) fun m => Φ (m + 1)) :=
  wpish.unfold n Φ

example : wpish (PROP := PROP) = fixpoint wpish.pre := wpish.eq_fixpoint

end IrisTest.FixpointGuarded
