/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import IrisFix.Std.PointwiseLifting

/-! # Approximations

A fixpoint is computed in a domain `D` of approximations of values in `X`: `mem d x` says that
`d` approximates `x`, `hull T` is the best approximation of the set `T`, and `get d` is a value
that `d` approximates. Lifted pointwise to functions of the same arguments (`PointwiseLifting₂`),
`bind₂ S k` runs the body `k` on every function that `S` approximates, and approximates the
results pointwise. Every body gives a monotone `bind₂ · k`, so `partial_fixpoint` defines any body
`name := bind₂ name k`; then a property of the whole body `k` reads the fixpoint back:

* downsets (least and greatest fixpoints of `PROP`): `bind₂ S k = k S` for a monotone `k`
  (`bind₂_eq_downset`);
* balls (`Approx`, guarded fixpoints, `IrisFix.Algebra.Approx`): for a contractive `k`, the
  fixpoint is made of points, and their values are a fixpoint of `k` (`bind₂_get_approx`). -/

@[expose] public section

namespace Iris
open Lean.Order

open PointwiseLifting (rel all)

/-! ## Approximations -/

/-- `D` approximates values in `X`: `mem d x`, `d` approximates `x`; `hull T`, the best
approximation of the set `T`; and `get d`, a value that `d` approximates. -/
class Approximation (D : Type _) (X : Type _) where
  mem : D → X → Prop
  hull : (X → Prop) → D
  get : D → X
  mem_hull {T : X → Prop} {x : X} : T x → mem (hull T) x
  mem_get (d : D) : mem d (get d)

open Approximation PointwiseLifting₂

variable {D X : Type _} [Approximation D X] {PD PX : Type _} [PointwiseLifting D PD]
  [PointwiseLifting X PX] [PointwiseLifting₂ D X PD PX]

/-- Run the body `k` on every function that `S` approximates, and approximate the results. -/
def bind₂ (S : PD) (k : PX → PX) : PD :=
  hull₂ (hull (D := D) (X := X)) fun G => ∃ g, rel₂ (mem (D := D) (X := X)) S g ∧ G = k g

theorem bind₂_nonempty (S : PD) (k : PX → PX) :
    ∃ G, ∃ g, rel₂ (mem (D := D) (X := X)) S g ∧ G = k g :=
  ⟨_, _, rel₂_map₂ (mem_get (X := X)) S, rfl⟩

/-! ## Downsets -/

/-- `D` approximates itself by downsets: `d` approximates everything below it, and the best
approximation of a set is its supremum. -/
class Downsets (D : Type _) [PartialOrder D] [Approximation D D] : Prop where
  mem_iff (d x : D) : mem d x ↔ x ⊑ d
  hull_sup (T : D → Prop) : is_sup T (hull T)

/-- `D` approximates itself by downsets, with the supremum `sup`. -/
@[reducible] def Approximation.downsets {D : Type _} [PartialOrder D] (sup : (D → Prop) → D)
    (h : ∀ T, is_sup T (sup T)) : Approximation D D where
  mem d x := x ⊑ d
  hull := sup
  get d := d
  mem_hull hx := ((h _) _).1 PartialOrder.rel_refl _ hx
  mem_get _ := PartialOrder.rel_refl

section Downsets
variable {D : Type _} [PartialOrder D] [Approximation D D] [Downsets D]
  {PD : Type _} [PointwiseLifting D PD] [PointwiseLifting₂ D D PD PD] [PointwiseLiftingDiag D PD]
  [PartialOrder PD] [PointwiseLiftingLe D PD]
open Downsets (mem_iff hull_sup)
open PointwiseLiftingLe (le_iff)

omit [PointwiseLiftingDiag D PD] in
/-- Every body gives a monotone `bind₂ · k`: a larger `S` approximates more functions. -/
theorem bind₂_mono_downset {k : PD → PD} :
    monotone fun S : PD => bind₂ (D := D) (X := D) S k := fun S _ hS =>
  (le_iff (B := D)).2 <| hull₂_sub (R := (· ⊑ ·))
    (fun T T' hTT' _ => ((hull_sup T) _).2 fun z hz =>
      ((hull_sup T') _).1 PartialOrder.rel_refl z (hTT' z hz))
    (fun _ ⟨g, hg, e⟩ => ⟨g, rel₂_mono (fun _ _ ⟨_, h, hx⟩ =>
      (mem_iff _ _).2 (PartialOrder.rel_trans ((mem_iff _ _).1 hx) h))
      (rel₂_comp_r ((le_iff (B := D)).1 hS) hg), e⟩)
    (bind₂_nonempty S k)

/-- A monotone body runs on the fixpoint. -/
theorem bind₂_eq_downset {k : PD → PD} (hk : monotone k) (S : PD) :
    bind₂ (D := D) (X := D) S k = k S := by
  rw [← PointwiseLiftingDiag.map₂_id (B := D) (bind₂ (D := D) (X := D) S k)]
  refine hull₂_eq (R := (· ⊑ ·)) (e := id)
    (fun T x hx hle => PartialOrder.rel_antisymm (((hull_sup T) _).2 hle) (((hull_sup T) _).1
      PartialOrder.rel_refl x hx))
    ⟨S, PointwiseLiftingDiag.rel₂_iff.2 (PointwiseLifting.rel_mono
      (fun _ _ e => (mem_iff _ _).2 (e ▸ PartialOrder.rel_refl)) (PointwiseLifting.rel_eq S)),
      rfl⟩ ?_
  rintro _ ⟨g, hg, rfl⟩
  refine (le_iff (B := D)).1 (hk _ _ ((le_iff (B := D)).2 (PointwiseLifting.rel_flip ?_)))
  exact PointwiseLifting.rel_mono (fun _ _ h => (mem_iff _ _).1 h)
    (PointwiseLiftingDiag.rel₂_iff.1 hg)

end Downsets

/-- A fixpoint of `bind₂ · k`, for a monotone `k`, is a fixpoint of `k`. -/
theorem IsFix.of_bind₂_downset {D : Type _} [PartialOrder D] [Approximation D D] [Downsets D]
    {PD : Type _} [PointwiseLifting D PD] [PointwiseLifting₂ D D PD PD] [PointwiseLiftingDiag D PD]
    [CCPO PD] [PointwiseLiftingLe D PD] {k : PD → PD} {fn : PD}
    (h : IsFix (fun S => bind₂ (D := D) (X := D) S k) fn) (hk : monotone k) : IsFix k fn :=
  h.congr (bind₂_eq_downset hk)

end Iris
