/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import IrisFix.BI.Lib.Pointwise
public meta import IrisFix.ProofMode.Lib

@[expose] public section
open Iris BI OFE Lean.Order

namespace IrisTest.Pointwise

local bi PROP

variable {PROP : Type _} [BI PROP]

/-! ## The generic law is the unary laws -/

section
variable {A : Type _} {F : (A → PROP) → A → PROP} (h : BIMono F)

open MonotoneFixpoint in
example (Φ : A → PROP) : ⊢ □ (∀ x, F Φ x -∗ Φ x) -∗ ∀ x, lfp F h x -∗ Φ x :=
  IOrder.fix_iter h Φ

open CoMonotoneFixpoint in
example (Φ : A → PROP) : ⊢ □ (∀ x, Φ x -∗ F Φ x) -∗ ∀ x, Φ x -∗ gfp F h x :=
  IOrder.fix_iter (fun Φ Ψ => h Ψ Φ) Φ

open MonotoneFixpoint in
example (G : (A → PROP) → A → PROP) (g : A → PROP) (hg : ∀ x, G g x ⊢ g x) :
    ⊢ □ (∀ Φ x, F Φ x -∗ G Φ x) -∗ ∀ x, lfp F h x -∗ g x :=
  IOrder.fix_strong_mono h G g hg

open CoMonotoneFixpoint in
example (G : (A → PROP) → A → PROP) (g : A → PROP) (hg : ∀ x, g x ⊢ G g x) :
    ⊢ □ (∀ Φ x, G Φ x -∗ F Φ x) -∗ ∀ x, g x -∗ gfp F h x :=
  IOrder.fix_strong_mono (fun Φ Ψ => h Ψ Φ) G g hg

open MonotoneFixpoint in
example (Φ : A → PROP) :
    ⊢ □ (∀ x, F (fun y => iprop(Φ y ∧ lfp F h y)) x -∗ Φ x) -∗ ∀ x, lfp F h x -∗ Φ x :=
  IOrder.fix_ind h Φ

open CoMonotoneFixpoint in
example (Φ : A → PROP) :
    ⊢ □ (∀ x, Φ x -∗ F (fun y => iprop(Φ y ∨ gfp F h y)) x) -∗ ∀ x, Φ x -∗ gfp F h x :=
  IOrder.fix_ind (fun Φ Ψ => h Ψ Φ) Φ

open MonotoneFixpoint in
example (Φ W : A → PROP) (hW : ∀ x, iprop(Φ x ∧ F W x) ⊢ W x) :
    ⊢ □ (∀ x, F W x -∗ Φ x) -∗ ∀ x, lfp F h x -∗ Φ x :=
  IOrder.fix_ind_wf h Φ W hW

open CoMonotoneFixpoint in
example (Φ W : A → PROP) (hW : ∀ x, W x ⊢ iprop(Φ x ∨ F W x)) :
    ⊢ □ (∀ x, Φ x -∗ F W x) -∗ ∀ x, Φ x -∗ gfp F h x :=
  IOrder.fix_ind_wf (fun Φ Ψ => h Ψ Φ) Φ W hW
end

section
variable {A : Type _} {F : (A → PROP) → A → PROP} (h : BIMono F)

section
open MonotoneFixpoint

-- Park induction alone, at a constant.
example [∀ x, Affine (F (fun _ => iprop(emp)) x)] (x : A) : Affine (lfp F h x) :=
  ⟨IOrder.fix_le_of (monotone_of_bimono h) (E := fun _ => iprop(emp)) (fun _ => Affine.affine) x⟩

example [∀ x, Absorbing (F (fun y => iprop(True -∗ lfp F h y)) x)] (x : A) :
    Absorbing (lfp F h x) := by
  have hT (P : PROP) : iprop(True -∗ P) ⊢ P := by iintro H; iapply H; ipureintro; trivial
  have hA (P : PROP) [Absorbing P] : P ⊢ iprop(True -∗ P) := by iintro H -; iexact H
  have hle := IOrder.fix_le_imap (PROP := PROP) (monotone_of_bimono h)
    (m := fun P => iprop(True -∗ P)) wand_mono_right (fun _ => hT _) (fun _ => hA _)
  exact ⟨sep_symm.trans (wand_elim (hle x))⟩

example [∀ x, Affine (F (fun y => iprop(□ lfp F h y)) x)]
    [∀ x, Persistent (F (fun y => iprop(□ lfp F h y)) x)] (x : A) : Persistent (lfp F h x) := by
  have hle := IOrder.fix_le_imap (PROP := PROP) (monotone_of_bimono h) (m := fun P => iprop(□ P))
    intuitionistically_mono (fun _ => intuitionistically_elim)
    (fun _ => intuitionistically_of_intuitionistic.2)
  exact ⟨(hle x).trans persistently_of_intuitionistically⟩

example [∀ x, Absorbing (lfp F h x)] [∀ x, Persistent (F (fun y => iprop(<pers> lfp F h y)) x)]
    (x : A) : Persistent (lfp F h x) := by
  have hle := IOrder.fix_le_imap (PROP := PROP) (monotone_of_bimono h)
    (m := fun P => iprop(<pers> P))
    persistently_mono (fun _ => persistently_elim) (fun _ => Persistent.persistent)
  exact ⟨hle x⟩
end

section
open CoMonotoneFixpoint

example [∀ x, Absorbing (F (fun y => iprop(<absorb> gfp F h y)) x)] (x : A) :
    Absorbing (gfp F h x) := by
  have hle := IOrder.fix_le_imap (PROP := PROP) (monotone_of_bimono h)
    (m := fun P => iprop(<absorb> P))
    absorbingly_mono (fun _ => absorbingly_intro) (fun _ => Absorbing.absorbing)
  exact ⟨hle x⟩
end
end

/-! ## The unary `ne` laws -/

section
variable {A : Type _} {F : (A → PROP) → A → PROP} (h : BIMono F)

open MonotoneFixpoint in
example [OFE A] (hF : ∀ Φ : A → PROP, NonExpansive Φ → NonExpansive (F Φ)) :
    NonExpansive (lfp F h) := by
  -- `ne` at `A → PROP` is non-expansiveness.
  have hne := IOrder.fix_ne (PROP := PROP) (monotone_of_bimono h) fun f hf n x y hxy =>
    (hF f ⟨fun {n} x y => hf n x y⟩).ne hxy
  exact ⟨fun {n} x y => hne n x y⟩

open CoMonotoneFixpoint in
example [OFE A] (hF : ∀ Φ : A → PROP, NonExpansive Φ → NonExpansive (F Φ)) :
    NonExpansive (gfp F h) := by
  -- `ne` at `A → PROP` is non-expansiveness.
  have hne := IOrder.fix_ne (PROP := PROP) (monotone_of_bimono h) fun f hf n x y hxy =>
    (hF f ⟨fun {n} x y => hf n x y⟩).ne hxy
  exact ⟨fun {n} x y => hne n x y⟩

open MonotoneFixpoint in
example {F₁ F₂ : (A → PROP) → A → PROP} (h₁ : BIMono F₁) (h₂ : BIMono F₂) {n : Nat}
    (hF₂ : ∀ Φ Ψ : A → PROP, (∀ x, Φ x ≡{n}≡ Ψ x) → ∀ x, F₂ Φ x ≡{n}≡ F₂ Ψ x)
    (hF : ∀ Φ x, F₁ Φ x ≡{n}≡ F₂ Φ x) (x : A) : lfp F₁ h₁ x ≡{n}≡ lfp F₂ h₂ x :=
  IOrder.fix_dist PROP (monotone_of_bimono h₁) (monotone_of_bimono h₂) hF₂ hF x

open CoMonotoneFixpoint in
example {F₁ F₂ : (A → PROP) → A → PROP} (h₁ : BIMono F₁) (h₂ : BIMono F₂) {n : Nat}
    (hF₂ : ∀ Φ Ψ : A → PROP, (∀ x, Φ x ≡{n}≡ Ψ x) → ∀ x, F₂ Φ x ≡{n}≡ F₂ Ψ x)
    (hF : ∀ Φ x, F₁ Φ x ≡{n}≡ F₂ Φ x) (x : A) : gfp F₁ h₁ x ≡{n}≡ gfp F₂ h₂ x :=
  IOrder.fix_dist PROP (monotone_of_bimono h₁) (monotone_of_bimono h₂) hF₂ hF x
end

-- Two arguments with OFEs: non-expansive in both.
section
open MonotoneFixpoint
variable {α γ : Type _} [OFE α] [OFE γ] {F : (α → γ → PROP) → α → γ → PROP} (hF : monotone F)

def NE₂ (f : α → γ → PROP) : Prop :=
  ∀ n x x', x ≡{n}≡ x' → ∀ y y', y ≡{n}≡ y' → f x y ≡{n}≡ f x' y'

example (hne : ∀ f, NE₂ (PROP := PROP) f → NE₂ (F f)) {n : Nat} {x x' : α} {y y' : γ}
    (hx : x ≡{n}≡ x') (hy : y ≡{n}≡ y') : fix F hF x y ≡{n}≡ fix F hF x' y' :=
  IOrder.fix_ne (PROP := PROP) hF hne n x x' hx y y' hy
end

/-! ## Every law at two arguments

The monotonicity hypotheses are stated without `IOrder`: they are `IMono` by unfolding. -/

section
open MonotoneFixpoint
variable {F : (Nat → Bool → PROP) → Nat → Bool → PROP}
  (hF : ∀ Φ Ψ : Nat → Bool → PROP, ⊢ □ (∀ n b, Φ n b -∗ Ψ n b) -∗ ∀ n b, F Φ n b -∗ F Ψ n b)

local notation "μ" => fix F (IOrder.monotone_of_imono hF)

example (Φ : Nat → Bool → PROP) : ⊢ □ (∀ n b, F Φ n b -∗ Φ n b) -∗ ∀ n b, μ n b -∗ Φ n b :=
  IOrder.fix_iter hF Φ

example (G : (Nat → Bool → PROP) → Nat → Bool → PROP) (g : Nat → Bool → PROP)
    (hg : ∀ n b, G g n b ⊢ g n b) :
    ⊢ □ (∀ Φ n b, F Φ n b -∗ G Φ n b) -∗ ∀ n b, μ n b -∗ g n b :=
  IOrder.fix_strong_mono hF G g hg

example (Φ : Nat → Bool → PROP) :
    ⊢ □ (∀ n b, F (fun n b => iprop(Φ n b ∧ μ n b)) n b -∗ Φ n b) -∗ ∀ n b, μ n b -∗ Φ n b :=
  IOrder.fix_ind hF Φ

example (Φ W : Nat → Bool → PROP) (hW : ∀ n b, iprop(Φ n b ∧ F W n b) ⊢ W n b) :
    ⊢ □ (∀ n b, F W n b -∗ Φ n b) -∗ ∀ n b, μ n b -∗ Φ n b :=
  IOrder.fix_ind_wf hF Φ W hW

example [∀ n b, Affine (F (fun _ _ => iprop(emp)) n b)] (n : Nat) (b : Bool) : Affine (μ n b) :=
  ⟨IOrder.fix_le_of (IOrder.monotone_of_imono hF) (E := fun _ _ => iprop(emp))
    (fun _ _ => Affine.affine) n b⟩

example [∀ n b, Absorbing (F (fun n b => iprop(True -∗ μ n b)) n b)] (n : Nat) (b : Bool) :
    Absorbing (μ n b) := by
  have hT (P : PROP) : iprop(True -∗ P) ⊢ P := by iintro H; iapply H; ipureintro; trivial
  have hA (P : PROP) [Absorbing P] : P ⊢ iprop(True -∗ P) := by iintro H -; iexact H
  have hle := IOrder.fix_le_imap (PROP := PROP) (IOrder.monotone_of_imono hF)
    (m := fun P => iprop(True -∗ P)) wand_mono_right (fun _ _ => hT _) (fun _ _ => hA _)
  exact ⟨sep_symm.trans (wand_elim (hle n b))⟩

example [∀ n b, Affine (F (fun n b => iprop(□ μ n b)) n b)]
    [∀ n b, Persistent (F (fun n b => iprop(□ μ n b)) n b)] (n : Nat) (b : Bool) :
    Persistent (μ n b) := by
  have hle := IOrder.fix_le_imap (PROP := PROP) (IOrder.monotone_of_imono hF)
    (m := fun P => iprop(□ P)) intuitionistically_mono (fun _ _ => intuitionistically_elim)
    (fun _ _ => intuitionistically_of_intuitionistic.2)
  exact ⟨(hle n b).trans persistently_of_intuitionistically⟩

example [∀ n b, Absorbing (μ n b)] [∀ n b, Persistent (F (fun n b => iprop(<pers> μ n b)) n b)]
    (n : Nat) (b : Bool) : Persistent (μ n b) := by
  have hle := IOrder.fix_le_imap (PROP := PROP) (IOrder.monotone_of_imono hF)
    (m := fun P => iprop(<pers> P)) persistently_mono (fun _ _ => persistently_elim)
    (fun _ _ => Persistent.persistent)
  exact ⟨hle n b⟩

example {F' : (Nat → Bool → PROP) → Nat → Bool → PROP}
    (hF' : ∀ Φ Ψ : Nat → Bool → PROP, ⊢ □ (∀ n b, Φ n b -∗ Ψ n b) -∗ ∀ n b, F' Φ n b -∗ F' Ψ n b)
    {k : Nat}
    (hF₂ : ∀ Φ Ψ : Nat → Bool → PROP, (∀ n b, Φ n b ≡{k}≡ Ψ n b) → ∀ n b, F' Φ n b ≡{k}≡ F' Ψ n b)
    (hFF : ∀ Φ n b, F Φ n b ≡{k}≡ F' Φ n b) (n : Nat) (b : Bool) :
    μ n b ≡{k}≡ fix F' (IOrder.monotone_of_imono hF') n b :=
  IOrder.fix_dist PROP _ _ hF₂ hFF n b
end

section
open CoMonotoneFixpoint
variable {F : (Nat → Bool → PROP) → Nat → Bool → PROP}
  (hF : ∀ Φ Ψ : Nat → Bool → PROP, ⊢ □ (∀ n b, Ψ n b -∗ Φ n b) -∗ ∀ n b, F Ψ n b -∗ F Φ n b)

local notation "ν" => fix F (IOrder.monotone_of_imono hF)

example (Φ : Nat → Bool → PROP) : ⊢ □ (∀ n b, Φ n b -∗ F Φ n b) -∗ ∀ n b, Φ n b -∗ ν n b :=
  IOrder.fix_iter hF Φ

example (G : (Nat → Bool → PROP) → Nat → Bool → PROP) (g : Nat → Bool → PROP)
    (hg : ∀ n b, g n b ⊢ G g n b) :
    ⊢ □ (∀ Φ n b, G Φ n b -∗ F Φ n b) -∗ ∀ n b, g n b -∗ ν n b :=
  IOrder.fix_strong_mono hF G g hg

example (Φ : Nat → Bool → PROP) :
    ⊢ □ (∀ n b, Φ n b -∗ F (fun n b => iprop(Φ n b ∨ ν n b)) n b) -∗ ∀ n b, Φ n b -∗ ν n b :=
  IOrder.fix_ind hF Φ

example (Φ W : Nat → Bool → PROP) (hW : ∀ n b, W n b ⊢ iprop(Φ n b ∨ F W n b)) :
    ⊢ □ (∀ n b, Φ n b -∗ F W n b) -∗ ∀ n b, Φ n b -∗ ν n b :=
  IOrder.fix_ind_wf hF Φ W hW

example [∀ n b, Absorbing (F (fun n b => iprop(<absorb> ν n b)) n b)] (n : Nat) (b : Bool) :
    Absorbing (ν n b) := by
  have hle := IOrder.fix_le_imap (PROP := PROP) (IOrder.monotone_of_imono hF)
    (m := fun P => iprop(<absorb> P)) absorbingly_mono (fun _ _ => absorbingly_intro)
    (fun _ _ => Absorbing.absorbing)
  exact ⟨hle n b⟩

example {F' : (Nat → Bool → PROP) → Nat → Bool → PROP}
    (hF' : ∀ Φ Ψ : Nat → Bool → PROP, ⊢ □ (∀ n b, Ψ n b -∗ Φ n b) -∗ ∀ n b, F' Ψ n b -∗ F' Φ n b)
    {k : Nat}
    (hF₂ : ∀ Φ Ψ : Nat → Bool → PROP, (∀ n b, Φ n b ≡{k}≡ Ψ n b) → ∀ n b, F' Φ n b ≡{k}≡ F' Ψ n b)
    (hFF : ∀ Φ n b, F Φ n b ≡{k}≡ F' Φ n b) (n : Nat) (b : Bool) :
    ν n b ≡{k}≡ fix F' (IOrder.monotone_of_imono hF') n b :=
  IOrder.fix_dist PROP _ _ hF₂ hFF n b
end

/-! ## Curried laws for `partial_fixpoint` definitions -/

section
open MonotoneFixpoint

def evF (f : Nat → Bool → PROP) (_ : Nat) (b : Bool) : PROP := iprop(emp ∨ ∃ m, f m (!b))

def ev (_n : Nat) (b : Bool) : PROP := iprop(emp ∨ ∃ m, ev m (!b))
partial_fixpoint monotonicity IOrder.monotone_of_imono (PROP := PROP) (by imono)

example (hF : ∀ Φ Ψ : Nat → Bool → PROP,
      ⊢ □ (∀ n b, Φ n b -∗ Ψ n b) -∗ ∀ n b, evF Φ n b -∗ evF Ψ n b)
    (Φ : Nat → Bool → PROP) :
    ⊢ □ (∀ n b, evF Φ n b -∗ Φ n b) -∗ ∀ n b, ev n b -∗ Φ n b := by
  delta ev
  exact IOrder.fix_iter hF Φ
end

section
open CoMonotoneFixpoint

def stF (f : Nat → Bool → PROP) (n : Nat) (b : Bool) : PROP := iprop(▷ f (n + 1) (!b))

def st (n : Nat) (b : Bool) : PROP := iprop(▷ st (n + 1) (!b))
partial_fixpoint monotonicity IOrder.monotone_of_imono (PROP := PROP) (by imono)

example (hF : ∀ Φ Ψ : Nat → Bool → PROP,
      ⊢ □ (∀ n b, Ψ n b -∗ Φ n b) -∗ ∀ n b, stF Ψ n b -∗ stF Φ n b)
    (Φ : Nat → Bool → PROP) :
    ⊢ □ (∀ n b, Φ n b -∗ stF Φ n b) -∗ ∀ n b, Φ n b -∗ st n b := by
  delta st
  exact IOrder.fix_iter hF Φ
end

end IrisTest.Pointwise
