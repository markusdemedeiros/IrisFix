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
results pointwise.

* Monotonicity: `bind₂ · k` preserves extension for every body (`bind₂_ext`), so it is monotone
  whether `D` is ordered by extension (downsets: least and greatest fixpoints of `PROP`) or by
  information (balls, `IrisFix.Algebra.Approx`: guarded fixpoints). So `partial_fixpoint` defines
  any body `name := bind₂ name k`.
* Reading back: the hull of a set with a greatest element reads back as that element, so
  `get ∘ bind₂ S k = k (get ∘ S)` when `k (get ∘ S)` is the greatest value of `k` at what `S`
  approximates (`get_bind₂`). For downsets this holds at every `S`, for a monotone `k`, so
  `bind₂ · k = k` (`bind₂_eq_downset`); for balls, at the fixpoint, for a contractive `k`, which
  makes it a single function (`bind₂_get_approx`). -/

@[expose] public section

namespace Iris
open Lean.Order

open PointwiseLifting (rel all)

/-! ## Approximations -/

/-- `D` approximates values in `X`: `mem d x`, `d` approximates `x`; `hull T`, the best
approximation of the set `T`, approximating more of a larger set; and `get d`, a value that `d`
approximates. -/
class Approximation (D : Type _) (X : Type _) where
  mem : D → X → Prop
  hull : (X → Prop) → D
  get : D → X
  mem_hull {T : X → Prop} {x : X} : T x → mem (hull T) x
  mem_get (d : D) : mem d (get d)
  hull_mono {T T' : X → Prop} : (∀ x, T x → T' x) → (∃ x, T x) →
    ∀ x, mem (hull T) x → mem (hull T') x

open Approximation PointwiseLifting₂

/-- The extension order: `d'` approximates everything that `d` approximates. -/
def Approximation.ext {D : Type _} (X : Type _) [Approximation D X] (d d' : D) : Prop :=
  ∀ x : X, mem d x → mem d' x

section Generic
variable {D X : Type _} [Approximation D X] {PD PX : Type _} [PointwiseLifting D PD]
  [PointwiseLifting X PX] [PointwiseLifting₂ D X PD PX]

local notation "memA" => mem (D := D) (X := X)
local notation "getA" => get (D := D) (X := X)
local notation "extA" => (ext X : D → D → Prop)

/-- Run the body `k` on every function that `S` approximates, and approximate the results. -/
def bind₂ (S : PD) (k : PX → PX) : PD :=
  hull₂ (hull (D := D) (X := X)) fun G => ∃ g, rel₂ memA S g ∧ G = k g

local notation "bindA" => bind₂ (D := D) (X := X)

theorem bind₂_nonempty (S : PD) (k : PX → PX) : ∃ G, ∃ g, rel₂ memA S g ∧ G = k g :=
  ⟨_, _, rel₂_map₂ (mem_get (X := X)) S, rfl⟩

/-! ## Monotonicity

`bind₂ · k` preserves extension, for every body: a larger `S` approximates more functions, and
the hull of their images is larger. A CCPO of approximations is ordered by extension (Kleene
iteration from below: downsets) or by information, the reverse (from above: balls); either way,
`bind₂ · k` is monotone. -/

/-- `bind₂ · k` preserves extension. -/
theorem bind₂_ext (k : PX → PX) {S S' : PD} (h : rel extA S S') :
    rel extA (bindA S k) (bindA S' k) :=
  hull₂_sub (fun _ _ hTT' hne => hull_mono hTT' hne)
    (fun _ ⟨g, hg, e⟩ => ⟨g, rel₂_mono (fun _ _ ⟨_, h, hx⟩ => h _ hx) (rel₂_comp h hg), e⟩)
    (bind₂_nonempty S k)

section Mono
variable [PartialOrder D] [PartialOrder PD] [PointwiseLiftingLe D PD] {k : PX → PX}
open PointwiseLifting (rel_mono rel_flip)
open PointwiseLiftingLe (le_iff)

/-- In the extension order, `bind₂ · k` is monotone. -/
theorem bind₂_mono_ext (h : ∀ d d' : D, d ⊑ d' ↔ ext X d d') :
    monotone fun S : PD => bindA S k := fun _ _ hS =>
  (le_iff (B := D)).2 <| rel_mono (fun _ _ => (h _ _).2) <|
    bind₂_ext k <| rel_mono (fun _ _ => (h _ _).1) ((le_iff (B := D)).1 hS)

/-- In the information order, `bind₂ · k` is monotone. -/
theorem bind₂_mono_info (h : ∀ d d' : D, d ⊑ d' ↔ ext X d' d) :
    monotone fun S : PD => bindA S k := fun _ _ hS =>
  (le_iff (B := D)).2 <| rel_mono (fun _ _ => (h _ _).2) <| rel_flip <|
    bind₂_ext k <| rel_flip <| rel_mono (fun _ _ => (h _ _).1) ((le_iff (B := D)).1 hS)

end Mono

/-! ## Reading back

The best approximation of a set with a greatest element reads back as that element. So if the
body sends what `S` approximates to values with a greatest one, `k (get ∘ S)`, then `bind₂ S k`
reads back as `k (get ∘ S)`. Downsets: everywhere, for a monotone `k`. Balls: at the fixpoint, for
a contractive `k`, which makes the fixpoint a single function. -/

section ReadBack
variable {R : X → X → Prop} {k : PX → PX} {S : PD}

/-- `bind₂ S k` reads back as `k (get ∘ S)`, if that is the greatest value of `k` at what `S`
approximates, along an `R` for which a hull reads back as the greatest element of its set. -/
theorem get_bind₂ (hhull : ∀ (T : X → Prop) x, T x → (∀ y, T y → R y x) → getA (hull T) = x)
    (htop : ∀ g, rel₂ memA S g → rel R (k g) (k (map₂ getA S))) :
    map₂ getA (bindA S k) = k (map₂ getA S) :=
  hull₂_eq hhull ⟨_, rel₂_map₂ mem_get S, rfl⟩ fun _ ⟨g, hg, e⟩ => e ▸ htop g hg

/-- At a fixpoint of `bind₂ · k`, if `k (get ∘ S)` is the greatest value of `k` at what `S`
approximates, `get ∘ S` is a fixpoint of `k`. -/
theorem get_fix (hhull : ∀ (T : X → Prop) x, T x → (∀ y, T y → R y x) → getA (hull T) = x)
    (hS : S = bindA S k) (htop : ∀ g, rel₂ memA S g → rel R (k g) (k (map₂ getA S))) :
    map₂ getA S = k (map₂ getA S) :=
  (congrArg (map₂ getA) hS).trans (get_bind₂ hhull htop)

end ReadBack

end Generic

/-! ## Downsets -/

/-- `D` approximates itself by downsets: `d` approximates everything below it, the best
approximation of a set is its supremum, and `d` reads back as itself. -/
class Downsets (D : Type _) [PartialOrder D] [Approximation D D] : Prop where
  mem_iff (d x : D) : mem d x ↔ x ⊑ d
  hull_sup (T : D → Prop) : is_sup T (hull T)
  get_eq (d : D) : get d = d

/-- `D` approximates itself by downsets, with the supremum `sup`. -/
@[reducible] def Approximation.downsets {D : Type _} [PartialOrder D] (sup : (D → Prop) → D)
    (h : ∀ T, is_sup T (sup T)) : Approximation D D where
  mem d x := x ⊑ d
  hull := sup
  get d := d
  mem_hull hx := ((h _) _).1 PartialOrder.rel_refl _ hx
  mem_get _ := PartialOrder.rel_refl
  hull_mono hTT' _ _ hx := PartialOrder.rel_trans hx <|
    ((h _) _).2 fun y hy => ((h _) _).1 PartialOrder.rel_refl y (hTT' y hy)

section Downsets
variable {D : Type _} [PartialOrder D] [Approximation D D] [Downsets D]
  {PD : Type _} [PointwiseLifting D PD] [PointwiseLifting₂ D D PD PD] [PointwiseLiftingDiag D PD]
  [PartialOrder PD] [PointwiseLiftingLe D PD]
open Downsets (mem_iff hull_sup get_eq)
open PointwiseLiftingLe (le_iff)

/-- Downsets are ordered by extension. -/
theorem Downsets.le_iff_ext (d d' : D) : d ⊑ d' ↔ ext D d d' :=
  ⟨fun h _ hx => (mem_iff _ _).2 (PartialOrder.rel_trans ((mem_iff _ _).1 hx) h),
    fun h => (mem_iff _ _).1 (h d ((mem_iff _ _).2 PartialOrder.rel_refl))⟩

omit [PointwiseLiftingDiag D PD] in
/-- Every body gives a monotone `bind₂ · k`. -/
theorem bind₂_mono_downset {k : PD → PD} : monotone fun S : PD => bind₂ (D := D) (X := D) S k :=
  bind₂_mono_ext Downsets.le_iff_ext

/-- A monotone body runs on the fixpoint: `k S` is the greatest value of `k` below `S`. -/
theorem bind₂_eq_downset {k : PD → PD} (hk : monotone k) (S : PD) :
    bind₂ (D := D) (X := D) S k = k S := by
  have e : map₂ (get (D := D) (X := D)) = (id : PD → PD) := by
    rw [show (get : D → D) = id from funext get_eq]; exact funext PointwiseLiftingDiag.map₂_id
  have h := get_bind₂ (D := D) (R := (· ⊑ ·)) (S := S) (k := k)
    (fun T x hx hle => (get_eq _).trans <| PartialOrder.rel_antisymm (((hull_sup T) _).2 hle)
      (((hull_sup T) _).1 PartialOrder.rel_refl x hx))
    (fun g hg => (le_iff (B := D)).1 <| hk _ _ <| (le_iff (B := D)).2 <| by
      rw [e]; exact PointwiseLifting.rel_flip <| PointwiseLifting.rel_mono
        (fun _ _ h => (mem_iff _ _).1 h) (PointwiseLiftingDiag.rel₂_iff.1 hg))
  rwa [e] at h

end Downsets

/-- A fixpoint of `bind₂ · k`, for a monotone `k`, is a fixpoint of `k`. -/
theorem IsFix.of_bind₂_downset {D : Type _} [PartialOrder D] [Approximation D D] [Downsets D]
    {PD : Type _} [PointwiseLifting D PD] [PointwiseLifting₂ D D PD PD] [PointwiseLiftingDiag D PD]
    [CCPO PD] [PointwiseLiftingLe D PD] {k : PD → PD} {fn : PD}
    (h : IsFix (fun S => bind₂ (D := D) (X := D) S k) fn) (hk : monotone k) : IsFix k fn :=
  h.congr (bind₂_eq_downset hk)

end Iris
