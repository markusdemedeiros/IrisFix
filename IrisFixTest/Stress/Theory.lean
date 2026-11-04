module

public import Iris.BI
public import IrisFix.ProofMode.Lib.Fixpoint
public import IrisFix.BI.Lib.FixpointBanach

/-! Stress tests for the theory/instance layer: `IOrder`, `IMeet`, `INe`, `PointwiseLifting*`,
`IPointwiseLifting`, at many `Pred` shapes, without the commands. -/

@[expose] public section
open Iris BI OFE

namespace IrisTest.Stress.Theory

local bi PROP

variable {PROP : Type _} [BI PROP]
open PointwiseLifting (all)

/-! ## Instance resolution at many shapes -/

section Synth
open MonotoneFixpoint

example : IOrder PROP PROP := inferInstance
example : IMeet PROP PROP := inferInstance
example : INe PROP := inferInstance
example : IOrder PROP (Nat → PROP) := inferInstance
example : IMeet PROP (Nat → PROP) := inferInstance
example : INe (Nat → PROP) := inferInstance
example : IOrder PROP (Unit → PROP) := inferInstance
example : IOrder PROP (Empty → PROP) := inferInstance
example : IOrder PROP (PROP → PROP) := inferInstance
example : IMeet PROP (PROP → PROP) := inferInstance
example : INe (PROP → PROP) := inferInstance
example : IOrder PROP ((Nat → PROP) → PROP) := inferInstance
example : INe ((Nat → PROP) → PROP) := inferInstance
example : IOrder PROP ((x : Nat) → Fin x → PROP) := inferInstance
example : INe ((x : Nat) → Fin x → PROP) := inferInstance
example : PointwiseLiftingLe PROP (Nat → Bool → PROP) := inferInstance
example : IPointwiseLifting PROP (Nat → Bool → PROP) := inferInstance
example : PointwiseLiftingLim PROP (Nat → PROP) := inferInstance
example : PointwiseLiftingLim PROP (PROP → PROP) := inferInstance
example : PointwiseLiftingLim PROP ((PROP → PROP) → Nat → PROP) := inferInstance
example : INe (Nat → PROP → Bool → PROP) := inferInstance
example : IMeet PROP (((PROP → PROP) → PROP) → ((Nat → PROP) → PROP) → PROP) := inferInstance
example : INe (((PROP → PROP) → PROP) → ((Nat → PROP) → PROP) → PROP) := inferInstance
example : IOrder PROP ((α : Type) → α → PROP) := inferInstance
example : INe ((α : Type) → α → PROP) := inferInstance
example : IOrder PROP ((α : Type 2) → α → PROP) := inferInstance
example : IOrder PROP (ULift.{3} Nat → PROP) := inferInstance

-- The low-priority lifting is not chosen at `PROP`, and agrees with the base instances there.
example : (inferInstance : IOrder PROP PROP) = instIOrderMonoProp := rfl
example : (IOrder.ofLifting (Pred := PROP) : IOrder PROP PROP) = instIOrderMonoProp := rfl
example : @IMeet.meet PROP _ PROP _ IOrder.ofLifting IMeet.ofLifting =
    @IMeet.meet PROP _ PROP _ _ instIMeetMonoProp := rfl

-- The order diamond (`CCPO.toPartialOrder` vs Lean's `instOrderPi`) closes at instance
-- transparency.
example : (Lean.Order.CCPO.toPartialOrder : Lean.Order.PartialOrder (Nat → PROP)) =
    Lean.Order.instOrderPi := by with_reducible_and_instances rfl
example : (Lean.Order.CCPO.toPartialOrder : Lean.Order.PartialOrder PROP) =
    instPartialOrderMonoProp := by with_reducible_and_instances rfl

-- `INe` picks `≡{n}≡` arguments where there is an OFE (`Unit`, `PROP`, `Nat → PROP`).
example (n : Nat) (f g : PROP → PROP) : INe.ne n f g ↔ ∀ P Q, P ≡{n}≡ Q → f P ≡{n}≡ g Q :=
  Iff.rfl
example (n : Nat) (f g : Unit → PROP) :
    INe.ne n f g ↔ ∀ x y : Unit, x ≡{n}≡ y → f x ≡{n}≡ g y := Iff.rfl
example (n : Nat) (f g : Nat → PROP) : INe.ne n f g ↔ ∀ x, f x ≡{n}≡ g x := Iff.rfl
example (n : Nat) (f g : (x : Nat) → Fin x → PROP) :
    INe.ne n f g ↔ ∀ x i, f x i ≡{n}≡ g x i := Iff.rfl
example (n : Nat) (f g : (Nat → PROP) → PROP) :
    INe.ne n f g ↔ ∀ Φ Ψ : Nat → PROP, Φ ≡{n}≡ Ψ → f Φ ≡{n}≡ g Ψ := Iff.rfl

end Synth

-- Failures are fast, and the low-priority lifting does not loop without a base.
section NoBase
variable [Lean.Order.CCPO PROP]
set_option synthInstance.maxHeartbeats 2000

/--
error: failed to synthesize
  IOrder PROP PROP

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in #synth IOrder PROP PROP

/--
error: failed to synthesize
  IOrder PROP (Nat → PROP)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in #synth IOrder PROP (Nat → PROP)
end NoBase

section NoBaseMeet
variable [Lean.Order.CCPO PROP] [IOrder PROP PROP]
example : IOrder PROP (Nat → PROP) := inferInstance
/--
error: failed to synthesize
  IMeet PROP (Nat → PROP)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in #synth IMeet PROP (Nat → PROP)
end NoBaseMeet

/-! ## Shapes: everything unfolds to the plain curried form -/

section Shapes
open MonotoneFixpoint

example (Φ : Nat → PROP) : all (B := PROP) Affine Φ ↔ ∀ x, Affine (Φ x) := Iff.rfl
example (Φ : PROP → PROP) : all (B := PROP) Affine Φ ↔ ∀ x, Affine (Φ x) := Iff.rfl
example (Φ : (PROP → PROP) → PROP) : all (B := PROP) Affine Φ ↔ ∀ x, Affine (Φ x) := Iff.rfl
example (Φ : (n : Nat) → Fin n → PROP) :
    all (B := PROP) Affine Φ ↔ ∀ n i, Affine (Φ n i) := Iff.rfl
example (Φ : PROP) : all (B := PROP) Affine Φ ↔ Affine Φ := Iff.rfl
example (Φ : Empty → PROP) : all (B := PROP) Affine Φ := fun e => e.elim

example (F : (PROP → PROP) → PROP → PROP) : IOrder.IMono PROP F ↔
    ∀ Φ Ψ : PROP → PROP, ⊢ □ (∀ P, Φ P -∗ Ψ P) -∗ ∀ P, F Φ P -∗ F Ψ P := Iff.rfl
example (Φ Ψ : PROP → PROP) : (Φ ⊑ᵢ Ψ) = iprop(∀ P, Φ P -∗ Ψ P) := rfl
example (Φ Ψ : PROP → PROP) : (Φ ⊑ᵢ Ψ) = iprop(∀ P, Φ P -∗ Ψ P) := by
  with_reducible_and_instances rfl
example (Φ Ψ : PROP → PROP) : Lean.Order.PartialOrder.rel Φ Ψ ↔ ∀ P, Φ P ⊢ Ψ P := Iff.rfl
example (Φ Ψ : PROP → PROP) : (Φ ⊓ᵢ Ψ) = fun P => iprop(Φ P ∧ Ψ P) := rfl
example (Φ Ψ : PROP → PROP) : (Φ ⊓ᵢ Ψ) = fun P => iprop(Φ P ∧ Ψ P) := by
  with_reducible_and_instances rfl
example (Φ Ψ : Nat → Bool → PROP) : (Φ ⊓ᵢ Ψ) = fun n b => iprop(Φ n b ∧ Ψ n b) := rfl
example (Φ Ψ : PROP → PROP) (h : ⊢ Φ ⊑ᵢ Ψ) : ⊢ ∀ P, Φ P -∗ Ψ P := by
  simp only [IOrder.le] at h
  exact h
example (Φ Ψ : PROP → PROP) (h : ⊢ Φ ⊑ᵢ Ψ) : ⊢ ∀ P, Φ P -∗ Ψ P := by
  dsimp only [IOrder.le, IPointwiseLifting.irel] at h
  exact h
end Shapes

section ShapesCo
open CoMonotoneFixpoint
example (Φ Ψ : PROP → PROP) : (Φ ⊑ᵢ Ψ) = iprop(∀ P, Ψ P -∗ Φ P) := rfl
example (Φ Ψ : PROP → PROP) : (Φ ⊓ᵢ Ψ) = fun P => iprop(Φ P ∨ Ψ P) := rfl
end ShapesCo

/-! ## The generic laws at many shapes -/

section LawsMono
open MonotoneFixpoint
open Lean.Order (fix)

example {F : PROP → PROP} (h : IOrder.IMono PROP F) (Φ : PROP) :
    ⊢ □ (F Φ -∗ Φ) -∗ fix F (IOrder.monotone_of_imono h) -∗ Φ :=
  IOrder.fix_iter h Φ

example {F : PROP → PROP} (h : IOrder.IMono PROP F) (Φ : PROP) :
    ⊢ □ (F iprop(Φ ∧ fix F (IOrder.monotone_of_imono h)) -∗ Φ) -∗
      fix F (IOrder.monotone_of_imono h) -∗ Φ :=
  IOrder.fix_ind h Φ

example {F : (Unit → PROP) → Unit → PROP} (h : IOrder.IMono PROP F) (Φ : Unit → PROP) :
    ⊢ □ (∀ u, F Φ u -∗ Φ u) -∗ ∀ u, fix F (IOrder.monotone_of_imono h) u -∗ Φ u :=
  IOrder.fix_iter h Φ

example {F : (Empty → PROP) → Empty → PROP} (h : IOrder.IMono PROP F) (Φ : Empty → PROP) :
    ⊢ □ (∀ u, F Φ u -∗ Φ u) -∗ ∀ u, fix F (IOrder.monotone_of_imono h) u -∗ Φ u :=
  IOrder.fix_iter h Φ

example {F : (PROP → PROP) → PROP → PROP} (h : IOrder.IMono PROP F) (Φ : PROP → PROP) :
    ⊢ □ (∀ P, F Φ P -∗ Φ P) -∗ ∀ P, fix F (IOrder.monotone_of_imono h) P -∗ Φ P :=
  IOrder.fix_iter h Φ

example {F : (PROP → PROP) → PROP → PROP} (h : IOrder.IMono PROP F) (Φ : PROP → PROP) :
    ⊢ □ (∀ P, F (fun Q => iprop(Φ Q ∧ fix F (IOrder.monotone_of_imono h) Q)) P -∗ Φ P) -∗
      ∀ P, fix F (IOrder.monotone_of_imono h) P -∗ Φ P :=
  IOrder.fix_ind h Φ

example {F : ((Nat → PROP) → PROP) → (Nat → PROP) → PROP} (h : IOrder.IMono PROP F)
    (Φ : (Nat → PROP) → PROP) :
    ⊢ □ (∀ P, F Φ P -∗ Φ P) -∗ ∀ P, fix F (IOrder.monotone_of_imono h) P -∗ Φ P :=
  IOrder.fix_iter h Φ

example {F : ((n : Nat) → Fin n → PROP) → (n : Nat) → Fin n → PROP} (h : IOrder.IMono PROP F)
    (Φ : (n : Nat) → Fin n → PROP) :
    ⊢ □ (∀ n i, F Φ n i -∗ Φ n i) -∗ ∀ n i, fix F (IOrder.monotone_of_imono h) n i -∗ Φ n i :=
  IOrder.fix_iter h Φ

universe v w in
example {A : Type v} {B : A → Type w} {F : ((a : A) → B a → PROP) → (a : A) → B a → PROP}
    (h : IOrder.IMono PROP F) (Φ : (a : A) → B a → PROP) :
    ⊢ □ (∀ a b, F Φ a b -∗ Φ a b) -∗ ∀ a b, fix F (IOrder.monotone_of_imono h) a b -∗ Φ a b :=
  IOrder.fix_iter h Φ

example {F : (PROP → PROP) → PROP → PROP} (h : IOrder.IMono PROP F)
    (G : (PROP → PROP) → PROP → PROP) (g : PROP → PROP) (hg : ∀ P, G g P ⊢ g P) :
    ⊢ □ (∀ Φ P, F Φ P -∗ G Φ P) -∗ ∀ P, fix F (IOrder.monotone_of_imono h) P -∗ g P :=
  IOrder.fix_strong_mono h G g hg

example {F : (PROP → PROP) → PROP → PROP} (h : IOrder.IMono PROP F) (Φ W : PROP → PROP)
    (hW : ∀ P, iprop(Φ P ∧ F W P) ⊢ W P) :
    ⊢ □ (∀ P, F W P -∗ Φ P) -∗ ∀ P, fix F (IOrder.monotone_of_imono h) P -∗ Φ P :=
  IOrder.fix_ind_wf h Φ W hW

-- Instance laws, with the base named.
example {F : (PROP → PROP) → PROP → PROP} (hF : Lean.Order.monotone F)
    (h : ∀ P, Affine (F (fun _ => iprop(emp)) P)) (P : PROP) : Affine (fix F hF P) :=
  IOrder.lfp_affine (PROP := PROP) hF h P

example {F : (PROP → PROP) → PROP → PROP} (hF : Lean.Order.monotone F)
    (h : ∀ P, Absorbing (F (fun Q => iprop(True -∗ fix F hF Q)) P)) (P : PROP) :
    Absorbing (fix F hF P) :=
  IOrder.lfp_absorbing (PROP := PROP) hF h P

example {F : PROP → PROP} (hF : Lean.Order.monotone F)
    (hA : Affine (F iprop(□ fix F hF))) (hP : Persistent (F iprop(□ fix F hF))) :
    Persistent (fix F hF) :=
  IOrder.lfp_persistent_affine (PROP := PROP) hF hA hP

example {F : ((n : Nat) → Fin n → PROP) → (n : Nat) → Fin n → PROP} (hF : Lean.Order.monotone F)
    (hA : ∀ n i, Absorbing (fix F hF n i))
    (hP : ∀ n i, Persistent (F (fun n i => iprop(<pers> fix F hF n i)) n i)) (n : Nat)
    (i : Fin n) : Persistent (fix F hF n i) :=
  IOrder.lfp_persistent_absorbing (PROP := PROP) hF hA hP n i

-- `ne`, at `PROP → PROP` (an OFE argument) and at `PROP`.
example {F : (PROP → PROP) → PROP → PROP} (hF : Lean.Order.monotone F) {n : Nat}
    (hne : ∀ f g : PROP → PROP, (∀ P Q, P ≡{n}≡ Q → f P ≡{n}≡ g Q) →
      ∀ P Q, P ≡{n}≡ Q → F f P ≡{n}≡ F g Q)
    {P Q : PROP} (h : P ≡{n}≡ Q) : fix F hF P ≡{n}≡ fix F hF Q :=
  fix_ne hF hF hne P Q h

example {F : PROP → PROP} (hF : Lean.Order.monotone F) {n : Nat}
    (hne : ∀ P Q : PROP, P ≡{n}≡ Q → F P ≡{n}≡ F Q) : fix F hF ≡{n}≡ fix F hF :=
  fix_ne hF hF hne

-- Pointwise `ne` at an OFE argument, by naming the instance.
example {F₁ F₂ : (Unit → PROP) → Unit → PROP} (h₁ : Lean.Order.monotone F₁)
    (h₂ : Lean.Order.monotone F₂) {n : Nat}
    (hF : ∀ Φ Ψ : Unit → PROP, (∀ x, Φ x ≡{n}≡ Ψ x) → ∀ x, F₁ Φ x ≡{n}≡ F₂ Ψ x) (x : Unit) :
    fix F₁ h₁ x ≡{n}≡ fix F₂ h₂ x :=
  @fix_ne _ _ INe.instPi _ _ h₁ h₂ n hF x

-- `PointwiseLifting.fix_all` directly.
example {F : (PROP → PROP) → PROP → PROP} (hF : Lean.Order.monotone F)
    (h : ∀ P, Persistent (F (fun Q => iprop(<pers> fix F hF Q)) P))
    (hA : ∀ P, Absorbing (fix F hF P)) (P : PROP) : Persistent (fix F hF P) :=
  PointwiseLifting.fix_all (B := PROP) hF (m := fun P => iprop(<pers> P))
    (fun _ _ => persistently_mono) (fun _ => ⟨fun h => h.persistent, fun h => ⟨h⟩⟩)
    (fun P => @persistently_elim _ _ _ (hA P)) h P

end LawsMono

section LawsCo
open CoMonotoneFixpoint
open Lean.Order (fix)

example {F : (PROP → PROP) → PROP → PROP} (h : IOrder.IMono PROP F) (Φ : PROP → PROP) :
    ⊢ □ (∀ P, Φ P -∗ F Φ P) -∗ ∀ P, Φ P -∗ fix F (IOrder.monotone_of_imono h) P :=
  IOrder.fix_iter h Φ

example {F : (PROP → PROP) → PROP → PROP} (h : IOrder.IMono PROP F) (Φ W : PROP → PROP)
    (hW : ∀ P, W P ⊢ iprop(Φ P ∨ F W P)) :
    ⊢ □ (∀ P, Φ P -∗ F W P) -∗ ∀ P, Φ P -∗ fix F (IOrder.monotone_of_imono h) P :=
  IOrder.fix_ind_wf h Φ W hW

example {F : (PROP → PROP) → PROP → PROP} (hF : Lean.Order.monotone F)
    (h : ∀ P, Absorbing (F (fun Q => iprop(<absorb> fix F hF Q)) P)) (P : PROP) :
    Absorbing (fix F hF P) :=
  IOrder.gfp_absorbing (PROP := PROP) hF h P

end LawsCo

/-! ## Banach laws at many shapes (base named) -/

section Banach

example (F : (PROP → PROP) → PROP → PROP) [Contractive F] {f : PROP → PROP} (hf : f = F f)
    (h : ∀ Φ : PROP → PROP, (∀ P, Persistent (Φ P)) → ∀ P, Persistent (F Φ P)) (P : PROP) :
    Persistent (f P) := Banach.fixpoint_persistent (PROP := PROP) F hf h P

example (F : PROP → PROP) [Contractive F] {f : PROP} (hf : f = F f)
    (h : ∀ Φ : PROP, Persistent Φ → Persistent (F Φ)) : Persistent f :=
  Banach.fixpoint_persistent (PROP := PROP) F hf h

example (F : (Unit → PROP) → Unit → PROP) [Contractive F] {f : Unit → PROP} (hf : f = F f)
    (h : ∀ Φ : Unit → PROP, (∀ P, Affine (Φ P)) → ∀ P, Affine (F Φ P)) (P : Unit) :
    Affine (f P) := Banach.fixpoint_affine (PROP := PROP) F hf h P

example (F : (Nat → PROP) → Nat → PROP) [Contractive F] {f : Nat → PROP} (hf : f = F f)
    (h : ∀ Φ : Nat → PROP, (∀ n, Persistent (Φ n)) → (∀ n, Absorbing (Φ n)) →
      ∀ n, Persistent (F Φ n) ∧ Absorbing (F Φ n)) (n : Nat) :
    Persistent (f n) ∧ Absorbing (f n) :=
  Banach.fixpoint_persistent_absorbing (PROP := PROP) F hf h n

example (F : ((PROP → PROP) → PROP) → (PROP → PROP) → PROP) [Contractive F]
    {f : (PROP → PROP) → PROP} (hf : f = F f)
    (h : ∀ Φ : (PROP → PROP) → PROP, (∀ P, Affine (Φ P)) → ∀ P, Affine (F Φ P))
    (P : PROP → PROP) : Affine (f P) := Banach.fixpoint_affine (PROP := PROP) F hf h P

example (F : (Empty → PROP) → Empty → PROP) [Contractive F] {f : Empty → PROP} (hf : f = F f)
    (h : ∀ Φ : Empty → PROP, (∀ P, Affine (Φ P)) → ∀ P, Affine (F Φ P)) (P : Empty) :
    Affine (f P) := Banach.fixpoint_affine (PROP := PROP) F hf h P

end Banach

/-! ## Explicit base, non-BI bodies -/

section ExplicitBase
open MonotoneFixpoint
open Lean.Order (fix)

-- The instance laws take `PROP` explicitly, so curried hypotheses elaborate without naming it.
example {F : (PROP → PROP) → PROP → PROP} (hF : Lean.Order.monotone F)
    (h : ∀ P, Affine (F (fun _ => iprop(emp)) P)) (P : PROP) : Affine (fix F hF P) :=
  IOrder.lfp_affine PROP hF h P

example (F : (Unit → PROP) → Unit → PROP) [Contractive F] {f : Unit → PROP} (hf : f = F f)
    (h : ∀ Φ : Unit → PROP, (∀ P, Affine (Φ P)) → ∀ P, Affine (F Φ P)) (P : Unit) :
    Affine (f P) := Banach.fixpoint_affine PROP F hf h P

end ExplicitBase

-- A body that only makes the recursive call (no BI operation) still keeps `[BI PROP]`.
ifix loop (a : Nat) : PROP := iprop% loop a

example (a : Nat) : (loop a : PROP) = loop.pre a (loop a) := loop.unfold a
example (a : Nat) (Φ : PROP) : ⊢ □ (loop.pre a Φ -∗ Φ) -∗ loop a -∗ Φ := loop.iter a Φ

/-! ## Limitations and bugs -/

section Bugs
open MonotoneFixpoint
open Lean.Order (fix)

-- Limitation: predicates with proof (`Sort 0`) arguments, e.g. `(n : Nat) → n < 5 → PROP`, have
-- no `PointwiseLifting`/`INe`/`IPointwiseLifting` instance: the `instPi`s take `ι : Type _`.
/--
error: failed to synthesize
  IOrder PROP ((n : Nat) → n < 5 → PROP)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in #synth IOrder PROP ((n : Nat) → n < 5 → PROP)

/--
error: failed to synthesize
  INe (1 = 1 → PROP)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in #synth INe (1 = 1 → PROP)

-- Limitation: the same, end to end: `ifix` rejects a proof argument with one error.
/--
error: ifix_monotone: the order of
  (n : Nat) → n < 5 → PROP
is not the order of `IOrder`
-/
#guard_msgs in
ifix bnd (n : Nat) (h : n < 5) : PROP :=
  iprop(⌜n = 0⌝ ∨ ∃ m, ∃ hm : m < 5, ⌜n = m + 1⌝ ∗ bnd m hm)

-- BUG: `⊑ᵢ` is opaque to the proof mode: the generic laws can't be `iapply`d without first
-- unfolding `IOrder.le`, even at `Pred = PROP`.
/--
error: iapply: IntoWand type class synthesis failed with IOrder.le (fix F ⋯) Φ and fix F ⋯
-/
#guard_msgs in
example {F : PROP → PROP} (h : IOrder.IMono PROP F) (Φ : PROP) (hΦ : F Φ ⊢ Φ) :
    fix F (IOrder.monotone_of_imono h) ⊢ Φ := by
  iintro H
  iapply IOrder.fix_iter h Φ $$ [] H
  iintro !> HF
  iapply hΦ $$ HF

-- The same, after unfolding: works.
example {F : PROP → PROP} (h : IOrder.IMono PROP F) (Φ : PROP) (hΦ : F Φ ⊢ Φ) :
    fix F (IOrder.monotone_of_imono h) ⊢ Φ := by
  have hi := IOrder.fix_iter h Φ
  simp only [IOrder.le] at hi
  iintro H
  iapply hi $$ [] H
  iintro !> HF
  iapply hΦ $$ HF

-- BUG: with six or more non-OFE arguments `CCPO` synthesis hits the default
-- `synthInstance.maxSize`, so the generic laws can't be stated in user code (the commands raise
-- the limit internally).
/--
error: failed to synthesize instance of type class
  Lean.Order.CCPO (Nat → Nat → Nat → Nat → Nat → Nat → PROP)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example {F : (Nat → Nat → Nat → Nat → Nat → Nat → PROP) → Nat → Nat → Nat → Nat → Nat → Nat → PROP}
    (h : IOrder.IMono PROP F) := IOrder.fix_iter h

set_option synthInstance.maxSize 1000 in
example {F : (Nat → Nat → Nat → Nat → Nat → Nat → PROP) → Nat → Nat → Nat → Nat → Nat → Nat → PROP}
    (h : IOrder.IMono PROP F) := IOrder.fix_iter h

-- Limitation: the high-priority `INe.instPiNE` always wins over `INe.instPi`, so pointwise `ne`
-- (`F₁` vs `F₂`) at an OFE argument needs the instance named (see `LawsMono`).
/--
error: Application type mismatch: The argument
  hF
has type
  ∀ (Φ Ψ : Unit → PROP), (∀ (x : Unit), Φ x ≡{n}≡ Ψ x) → ∀ (x : Unit), F₁ Φ x ≡{n}≡ F₂ Ψ x
but is expected to have type
  ∀ (f g : Unit → PROP), INe.ne ?m.26 f g → INe.ne ?m.26 (F₁ f) (F₂ g)
in the application
  fix_ne h₁ h₂ hF
-/
#guard_msgs in
example {F₁ F₂ : (Unit → PROP) → Unit → PROP} (h₁ : Lean.Order.monotone F₁)
    (h₂ : Lean.Order.monotone F₂) {n : Nat}
    (hF : ∀ Φ Ψ : Unit → PROP, (∀ x, Φ x ≡{n}≡ Ψ x) → ∀ x, F₁ Φ x ≡{n}≡ F₂ Ψ x) (x : Unit) :
    fix F₁ h₁ x ≡{n}≡ fix F₂ h₂ x :=
  fix_ne h₁ h₂ hF x

end Bugs

-- Limitation: with both scopes open, `CoMonotoneFixpoint` silently wins; a least-fixpoint law
-- then fails with a type mismatch rather than an ambiguity error.
section BothScopes
open MonotoneFixpoint CoMonotoneFixpoint
open Lean.Order (fix)
example : (inferInstance : Lean.Order.CCPO PROP) = instCCPOAntiProp := rfl
/--
error: Type mismatch
  IOrder.fix_iter h Φ
has type
  ⊢ □ IOrder.le (F Φ) Φ -∗ IOrder.le (fix F ⋯) Φ
but is expected to have type
  ⊢ (□ ∀ u, F Φ u -∗ Φ u) -∗ ∀ u, fix F ⋯ u -∗ Φ u
-/
#guard_msgs in
example {F : (Nat → PROP) → Nat → PROP} (h : IOrder.IMono PROP F) (Φ : Nat → PROP) :
    ⊢ □ (∀ u, F Φ u -∗ Φ u) -∗ ∀ u, fix F (IOrder.monotone_of_imono h) u -∗ Φ u :=
  IOrder.fix_iter h Φ
end BothScopes

-- Limitation: `open Lean.Order` brings core's scoped `⌜p⌝` notation, which breaks `⌜_⌝` inside
-- `iprop`.
section OpenOrder
open Lean.Order
/--
error: overloaded, errors ⏎
  failed to synthesize instance of type class
    CompleteLattice PROP
  ⏎
  Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
  ⏎
  elaboration function for `Iris.BI.BIBase.«term⌜_⌝»` has not been implemented
    ⌜True⌝
-/
#guard_msgs in
example : PROP := iprop% ⌜True⌝
end OpenOrder

end IrisTest.Stress.Theory
