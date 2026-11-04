/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import IrisFix.BI.Lib.Fixpoint
public meta import IrisFix.ProofMode.Lib

@[expose] public section
open Iris BI OFE Lean.Order

namespace IrisTest.FixpointLaws

local bi PROP

variable {PROP : Type _} [BI PROP]

/-! ## The generic law is the unary laws

`h : IMono PROP F` is monotonicity in the order of the open scope. -/

section
variable {A : Type _} {F : (A → PROP) → A → PROP}

-- The least (`μ`) and greatest (`ν`) fixpoint, at the `h` of each example.
set_option hygiene false in
local notation "μ" => fix F (IOrder.monotone_of_imono h)
set_option hygiene false in
local notation "ν" => fix F (IOrder.monotone_of_imono h)

open MonotoneFixpoint in
example (h : IOrder.IMono PROP F) (Φ : A → PROP) : ⊢ □ (∀ x, F Φ x -∗ Φ x) -∗ ∀ x, μ x -∗ Φ x :=
  (fix_isFix (IOrder.monotone_of_imono h)).iter h Φ

open CoMonotoneFixpoint in
example (h : IOrder.IMono PROP F) (Φ : A → PROP) : ⊢ □ (∀ x, Φ x -∗ F Φ x) -∗ ∀ x, Φ x -∗ ν x :=
  (fix_isFix (IOrder.monotone_of_imono h)).iter h Φ

open MonotoneFixpoint in
example (h : IOrder.IMono PROP F) (G : (A → PROP) → A → PROP) (g : A → PROP)
    (hg : ∀ x, G g x ⊢ g x) : ⊢ □ (∀ Φ x, F Φ x -∗ G Φ x) -∗ ∀ x, μ x -∗ g x :=
  (fix_isFix (IOrder.monotone_of_imono h)).strong_mono h G g hg

open CoMonotoneFixpoint in
example (h : IOrder.IMono PROP F) (G : (A → PROP) → A → PROP) (g : A → PROP)
    (hg : ∀ x, g x ⊢ G g x) : ⊢ □ (∀ Φ x, G Φ x -∗ F Φ x) -∗ ∀ x, g x -∗ ν x :=
  (fix_isFix (IOrder.monotone_of_imono h)).strong_mono h G g hg

open MonotoneFixpoint in
example (h : IOrder.IMono PROP F) (Φ : A → PROP) :
    ⊢ □ (∀ x, F (fun y => iprop(Φ y ∧ μ y)) x -∗ Φ x) -∗ ∀ x, μ x -∗ Φ x :=
  (fix_isFix (IOrder.monotone_of_imono h)).ind h Φ

open CoMonotoneFixpoint in
example (h : IOrder.IMono PROP F) (Φ : A → PROP) :
    ⊢ □ (∀ x, Φ x -∗ F (fun y => iprop(Φ y ∨ ν y)) x) -∗ ∀ x, Φ x -∗ ν x :=
  (fix_isFix (IOrder.monotone_of_imono h)).ind h Φ

open MonotoneFixpoint in
example (h : IOrder.IMono PROP F) (Φ W : A → PROP) (hW : ∀ x, iprop(Φ x ∧ F W x) ⊢ W x) :
    ⊢ □ (∀ x, F W x -∗ Φ x) -∗ ∀ x, μ x -∗ Φ x :=
  (fix_isFix (IOrder.monotone_of_imono h)).ind_wf h Φ W hW

open CoMonotoneFixpoint in
example (h : IOrder.IMono PROP F) (Φ W : A → PROP) (hW : ∀ x, W x ⊢ iprop(Φ x ∨ F W x)) :
    ⊢ □ (∀ x, Φ x -∗ F W x) -∗ ∀ x, Φ x -∗ ν x :=
  (fix_isFix (IOrder.monotone_of_imono h)).ind_wf h Φ W hW

section
open MonotoneFixpoint

-- Park induction alone, at a constant.
example (h : IOrder.IMono PROP F) [∀ x, Affine (F (fun _ => iprop(emp)) x)] (x : A) :
    Affine (μ x) :=
  ⟨(fix_isFix (IOrder.monotone_of_imono h)).le_of (IOrder.monotone_of_imono h)
    (E := fun _ => iprop(emp))
    (fun _ => Affine.affine) x⟩

example (h : IOrder.IMono PROP F) [∀ x, Absorbing (F (fun y => iprop(True -∗ μ y)) x)] (x : A) :
    Absorbing (μ x) := by
  have hT (P : PROP) : iprop(True -∗ P) ⊢ P := by iintro H; iapply H; ipureintro; trivial
  have hA (P : PROP) [Absorbing P] : P ⊢ iprop(True -∗ P) := by iintro H -; iexact H
  have hle := (fix_isFix (IOrder.monotone_of_imono h)).le_map (IOrder.monotone_of_imono h)
    (PointwiseLifting.map_mono (B := PROP) (m := fun P => iprop(True -∗ P))
      fun _ _ => wand_mono_right)
    (fun _ => hT _) (fun _ => hA _)
  exact ⟨sep_symm.trans (wand_elim (hle x))⟩

example (h : IOrder.IMono PROP F) [∀ x, Affine (F (fun y => iprop(□ μ y)) x)]
    [∀ x, Persistent (F (fun y => iprop(□ μ y)) x)] (x : A) : Persistent (μ x) := by
  have hle := (fix_isFix (IOrder.monotone_of_imono h)).le_map (IOrder.monotone_of_imono h)
    (PointwiseLifting.map_mono (B := PROP) (m := fun P => iprop(□ P))
      fun _ _ => intuitionistically_mono)
    (fun _ => intuitionistically_elim)
    (fun _ => intuitionistically_of_intuitionistic.2)
  exact ⟨(hle x).trans persistently_of_intuitionistically⟩

example (h : IOrder.IMono PROP F) [∀ x, Absorbing (μ x)]
    [∀ x, Persistent (F (fun y => iprop(<pers> μ y)) x)] (x : A) : Persistent (μ x) := by
  have hle := (fix_isFix (IOrder.monotone_of_imono h)).le_map (IOrder.monotone_of_imono h)
    (PointwiseLifting.map_mono (B := PROP) (m := fun P => iprop(<pers> P))
    fun _ _ => persistently_mono) (fun _ => persistently_elim) (fun _ => Persistent.persistent)
  exact ⟨hle x⟩
end

open CoMonotoneFixpoint in
example (h : IOrder.IMono PROP F) [∀ x, Absorbing (F (fun y => iprop(<absorb> ν y)) x)] (x : A) :
    Absorbing (ν x) := by
  have hle := (fix_isFix (IOrder.monotone_of_imono h)).le_map (IOrder.monotone_of_imono h)
    (PointwiseLifting.map_mono (B := PROP) (m := fun P => iprop(<absorb> P))
    fun _ _ => absorbingly_mono) (fun _ => absorbingly_intro) (fun _ => Absorbing.absorbing)
  exact ⟨hle x⟩

/-! ## The unary `ne` laws -/

open MonotoneFixpoint in
example [OFE A] (h : IOrder.IMono PROP F)
    (hF : ∀ n (Φ Ψ : A → PROP), (∀ x y, x ≡{n}≡ y → Φ x ≡{n}≡ Ψ y) →
      ∀ x y, x ≡{n}≡ y → F Φ x ≡{n}≡ F Ψ y) : NonExpansive μ :=
  -- `ne n` at `A → PROP` relates `Φ` and `Ψ` at `≡{n}≡` arguments.
  ⟨fun {n} x y hxy => fix_ne _ _ (hF n) x y hxy⟩

open CoMonotoneFixpoint in
example [OFE A] (h : IOrder.IMono PROP F)
    (hF : ∀ n (Φ Ψ : A → PROP), (∀ x y, x ≡{n}≡ y → Φ x ≡{n}≡ Ψ y) →
      ∀ x y, x ≡{n}≡ y → F Φ x ≡{n}≡ F Ψ y) : NonExpansive ν :=
  -- `ne n` at `A → PROP` relates `Φ` and `Ψ` at `≡{n}≡` arguments.
  ⟨fun {n} x y hxy => fix_ne _ _ (hF n) x y hxy⟩

open MonotoneFixpoint in
example {F₁ F₂ : (A → PROP) → A → PROP} (h₁ : IOrder.IMono PROP F₁) (h₂ : IOrder.IMono PROP F₂)
    {n : Nat} (hF₂ : ∀ Φ Ψ : A → PROP, (∀ x, Φ x ≡{n}≡ Ψ x) → ∀ x, F₂ Φ x ≡{n}≡ F₂ Ψ x)
    (hF : ∀ Φ x, F₁ Φ x ≡{n}≡ F₂ Φ x) (x : A) :
    fix F₁ (IOrder.monotone_of_imono h₁) x ≡{n}≡ fix F₂ (IOrder.monotone_of_imono h₂) x :=
  fix_ne _ _ (fun Φ Ψ hΦΨ x => (hF Φ x).trans (hF₂ Φ Ψ hΦΨ x)) x

open CoMonotoneFixpoint in
example {F₁ F₂ : (A → PROP) → A → PROP} (h₁ : IOrder.IMono PROP F₁) (h₂ : IOrder.IMono PROP F₂)
    {n : Nat} (hF₂ : ∀ Φ Ψ : A → PROP, (∀ x, Φ x ≡{n}≡ Ψ x) → ∀ x, F₂ Φ x ≡{n}≡ F₂ Ψ x)
    (hF : ∀ Φ x, F₁ Φ x ≡{n}≡ F₂ Φ x) (x : A) :
    fix F₁ (IOrder.monotone_of_imono h₁) x ≡{n}≡ fix F₂ (IOrder.monotone_of_imono h₂) x :=
  fix_ne _ _ (fun Φ Ψ hΦΨ x => (hF Φ x).trans (hF₂ Φ Ψ hΦΨ x)) x
end

-- Two arguments with OFEs: non-expansive in both.
section
open MonotoneFixpoint
variable {α γ : Type _} [OFE α] [OFE γ] {F : (α → γ → PROP) → α → γ → PROP} (hF : monotone F)

example {n : Nat} (hne : ∀ f g : α → γ → PROP,
      (∀ x x', x ≡{n}≡ x' → ∀ y y', y ≡{n}≡ y' → f x y ≡{n}≡ g x' y') →
      ∀ x x', x ≡{n}≡ x' → ∀ y y', y ≡{n}≡ y' → F f x y ≡{n}≡ F g x' y')
    {x x' : α} {y y' : γ} (hx : x ≡{n}≡ x') (hy : y ≡{n}≡ y') : fix F hF x y ≡{n}≡ fix F hF x' y' :=
  fix_ne hF hF hne x x' hx y y' hy
end

/-! ## Every law at two arguments

The monotonicity hypotheses are stated without `IOrder`: they are `IMono` by unfolding. -/

section
open MonotoneFixpoint
variable {F : (Nat → Bool → PROP) → Nat → Bool → PROP}
  (hF : ∀ Φ Ψ : Nat → Bool → PROP, ⊢ □ (∀ n b, Φ n b -∗ Ψ n b) -∗ ∀ n b, F Φ n b -∗ F Ψ n b)

local notation "μ" => fix F (IOrder.monotone_of_imono hF)

example (Φ : Nat → Bool → PROP) : ⊢ □ (∀ n b, F Φ n b -∗ Φ n b) -∗ ∀ n b, μ n b -∗ Φ n b :=
  (fix_isFix (IOrder.monotone_of_imono hF)).iter hF Φ

example (G : (Nat → Bool → PROP) → Nat → Bool → PROP) (g : Nat → Bool → PROP)
    (hg : ∀ n b, G g n b ⊢ g n b) :
    ⊢ □ (∀ Φ n b, F Φ n b -∗ G Φ n b) -∗ ∀ n b, μ n b -∗ g n b :=
  (fix_isFix (IOrder.monotone_of_imono hF)).strong_mono hF G g hg

example (Φ : Nat → Bool → PROP) :
    ⊢ □ (∀ n b, F (fun n b => iprop(Φ n b ∧ μ n b)) n b -∗ Φ n b) -∗ ∀ n b, μ n b -∗ Φ n b :=
  (fix_isFix (IOrder.monotone_of_imono hF)).ind hF Φ

example (Φ W : Nat → Bool → PROP) (hW : ∀ n b, iprop(Φ n b ∧ F W n b) ⊢ W n b) :
    ⊢ □ (∀ n b, F W n b -∗ Φ n b) -∗ ∀ n b, μ n b -∗ Φ n b :=
  (fix_isFix (IOrder.monotone_of_imono hF)).ind_wf hF Φ W hW

example [∀ n b, Affine (F (fun _ _ => iprop(emp)) n b)] (n : Nat) (b : Bool) : Affine (μ n b) :=
  ⟨(fix_isFix (IOrder.monotone_of_imono hF)).le_of (IOrder.monotone_of_imono hF)
    (E := fun _ _ => iprop(emp))
    (fun _ _ => Affine.affine) n b⟩

example [∀ n b, Absorbing (F (fun n b => iprop(True -∗ μ n b)) n b)] (n : Nat) (b : Bool) :
    Absorbing (μ n b) := by
  have hT (P : PROP) : iprop(True -∗ P) ⊢ P := by iintro H; iapply H; ipureintro; trivial
  have hA (P : PROP) [Absorbing P] : P ⊢ iprop(True -∗ P) := by iintro H -; iexact H
  have hle := (fix_isFix (IOrder.monotone_of_imono hF)).le_map (IOrder.monotone_of_imono hF)
    (PointwiseLifting.map_mono (B := PROP) (m := fun P => iprop(True -∗ P))
      fun _ _ => wand_mono_right)
    (fun _ _ => hT _) (fun _ _ => hA _)
  exact ⟨sep_symm.trans (wand_elim (hle n b))⟩

example [∀ n b, Affine (F (fun n b => iprop(□ μ n b)) n b)]
    [∀ n b, Persistent (F (fun n b => iprop(□ μ n b)) n b)] (n : Nat) (b : Bool) :
    Persistent (μ n b) := by
  have hle := (fix_isFix (IOrder.monotone_of_imono hF)).le_map (IOrder.monotone_of_imono hF)
    (PointwiseLifting.map_mono (B := PROP) (m := fun P => iprop(□ P))
      fun _ _ => intuitionistically_mono)
    (fun _ _ => intuitionistically_elim)
    (fun _ _ => intuitionistically_of_intuitionistic.2)
  exact ⟨(hle n b).trans persistently_of_intuitionistically⟩

example [∀ n b, Absorbing (μ n b)] [∀ n b, Persistent (F (fun n b => iprop(<pers> μ n b)) n b)]
    (n : Nat) (b : Bool) : Persistent (μ n b) := by
  have hle := (fix_isFix (IOrder.monotone_of_imono hF)).le_map (IOrder.monotone_of_imono hF)
    (PointwiseLifting.map_mono (B := PROP) (m := fun P => iprop(<pers> P))
      fun _ _ => persistently_mono)
    (fun _ _ => persistently_elim)
    (fun _ _ => Persistent.persistent)
  exact ⟨hle n b⟩

example {F' : (Nat → Bool → PROP) → Nat → Bool → PROP}
    (hF' : ∀ Φ Ψ : Nat → Bool → PROP, ⊢ □ (∀ n b, Φ n b -∗ Ψ n b) -∗ ∀ n b, F' Φ n b -∗ F' Ψ n b)
    {k : Nat}
    (hF₂ : ∀ Φ Ψ : Nat → Bool → PROP, (∀ n b, Φ n b ≡{k}≡ Ψ n b) → ∀ n b, F' Φ n b ≡{k}≡ F' Ψ n b)
    (hFF : ∀ Φ n b, F Φ n b ≡{k}≡ F' Φ n b) (n : Nat) (b : Bool) :
    μ n b ≡{k}≡ fix F' (IOrder.monotone_of_imono hF') n b :=
  fix_ne _ _ (fun Φ Ψ hΦΨ n b => (hFF Φ n b).trans (hF₂ Φ Ψ hΦΨ n b)) n b
end

section
open CoMonotoneFixpoint
variable {F : (Nat → Bool → PROP) → Nat → Bool → PROP}
  (hF : ∀ Φ Ψ : Nat → Bool → PROP, ⊢ □ (∀ n b, Ψ n b -∗ Φ n b) -∗ ∀ n b, F Ψ n b -∗ F Φ n b)

local notation "ν" => fix F (IOrder.monotone_of_imono hF)

example (Φ : Nat → Bool → PROP) : ⊢ □ (∀ n b, Φ n b -∗ F Φ n b) -∗ ∀ n b, Φ n b -∗ ν n b :=
  (fix_isFix (IOrder.monotone_of_imono hF)).iter hF Φ

example (G : (Nat → Bool → PROP) → Nat → Bool → PROP) (g : Nat → Bool → PROP)
    (hg : ∀ n b, g n b ⊢ G g n b) :
    ⊢ □ (∀ Φ n b, G Φ n b -∗ F Φ n b) -∗ ∀ n b, g n b -∗ ν n b :=
  (fix_isFix (IOrder.monotone_of_imono hF)).strong_mono hF G g hg

example (Φ : Nat → Bool → PROP) :
    ⊢ □ (∀ n b, Φ n b -∗ F (fun n b => iprop(Φ n b ∨ ν n b)) n b) -∗ ∀ n b, Φ n b -∗ ν n b :=
  (fix_isFix (IOrder.monotone_of_imono hF)).ind hF Φ

example (Φ W : Nat → Bool → PROP) (hW : ∀ n b, W n b ⊢ iprop(Φ n b ∨ F W n b)) :
    ⊢ □ (∀ n b, Φ n b -∗ F W n b) -∗ ∀ n b, Φ n b -∗ ν n b :=
  (fix_isFix (IOrder.monotone_of_imono hF)).ind_wf hF Φ W hW

example [∀ n b, Absorbing (F (fun n b => iprop(<absorb> ν n b)) n b)] (n : Nat) (b : Bool) :
    Absorbing (ν n b) := by
  have hle := (fix_isFix (IOrder.monotone_of_imono hF)).le_map (IOrder.monotone_of_imono hF)
    (PointwiseLifting.map_mono (B := PROP) (m := fun P => iprop(<absorb> P))
      fun _ _ => absorbingly_mono)
    (fun _ _ => absorbingly_intro)
    (fun _ _ => Absorbing.absorbing)
  exact ⟨hle n b⟩

example {F' : (Nat → Bool → PROP) → Nat → Bool → PROP}
    (hF' : ∀ Φ Ψ : Nat → Bool → PROP, ⊢ □ (∀ n b, Ψ n b -∗ Φ n b) -∗ ∀ n b, F' Ψ n b -∗ F' Φ n b)
    {k : Nat}
    (hF₂ : ∀ Φ Ψ : Nat → Bool → PROP, (∀ n b, Φ n b ≡{k}≡ Ψ n b) → ∀ n b, F' Φ n b ≡{k}≡ F' Ψ n b)
    (hFF : ∀ Φ n b, F Φ n b ≡{k}≡ F' Φ n b) (n : Nat) (b : Bool) :
    ν n b ≡{k}≡ fix F' (IOrder.monotone_of_imono hF') n b :=
  fix_ne _ _ (fun Φ Ψ hΦΨ n b => (hFF Φ n b).trans (hF₂ Φ Ψ hΦΨ n b)) n b
end

/-! ## Curried laws for `partial_fixpoint` definitions -/

section
open MonotoneFixpoint

def evF (f : Nat → Bool → PROP) (_ : Nat) (b : Bool) : PROP := iprop% emp ∨ ∃ m, f m (!b)

def ev (_n : Nat) (b : Bool) : PROP := iprop% emp ∨ ∃ m, ev m (!b)
partial_fixpoint monotonicity IOrder.monotone_of_imono (PROP := PROP) (by imono)

example (hF : ∀ Φ Ψ : Nat → Bool → PROP,
      ⊢ □ (∀ n b, Φ n b -∗ Ψ n b) -∗ ∀ n b, evF Φ n b -∗ evF Ψ n b)
    (Φ : Nat → Bool → PROP) :
    ⊢ □ (∀ n b, evF Φ n b -∗ Φ n b) -∗ ∀ n b, ev n b -∗ Φ n b := by
  delta ev
  exact (fix_isFix (IOrder.monotone_of_imono hF)).iter hF Φ
end

section
open CoMonotoneFixpoint

def stF (f : Nat → Bool → PROP) (n : Nat) (b : Bool) : PROP := iprop% ▷ f (n + 1) (!b)

def st (n : Nat) (b : Bool) : PROP := iprop% ▷ st (n + 1) (!b)
partial_fixpoint monotonicity IOrder.monotone_of_imono (PROP := PROP) (by imono)

example (hF : ∀ Φ Ψ : Nat → Bool → PROP,
      ⊢ □ (∀ n b, Ψ n b -∗ Φ n b) -∗ ∀ n b, stF Ψ n b -∗ stF Φ n b)
    (Φ : Nat → Bool → PROP) :
    ⊢ □ (∀ n b, Φ n b -∗ stF Φ n b) -∗ ∀ n b, Φ n b -∗ st n b := by
  delta st
  exact (fix_isFix (IOrder.monotone_of_imono hF)).iter hF Φ
end

end IrisTest.FixpointLaws
