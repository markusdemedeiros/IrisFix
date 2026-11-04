/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.Algebra.OFE
public import IrisFix.Std.Approximation

/-! # Approximations

The domain behind guarded fixpoints: balls of an OFE, ordered by reverse inclusion, form a `CCPO`.
Balls approximate the points they contain, and the best approximation of a set is its hull: an
`Approximation`. So `bind₂ · G` is monotone for every `G`, and for contractive `G` its fixpoint is
made of points, which are the Banach fixpoint of `G` (`bind₂_get_approx`, `eq_fixpoint`). A variant
of the formal balls of Edalat and Heckmann (TCS 193, 1998). -/

@[expose] public section

namespace Iris
open OFE Lean.Order

namespace Approx
-- TODO: This file must be generalized based on the step index changes.
variable {α : Type _} [OFE α]

/-- The ball around `c` determined by the set of levels `P`. -/
def ball (c : α) (P : Nat → Prop) : α → Prop := fun y => ∀ m, P m → c ≡{m}≡ y

/-- Levels at which all elements of `S` agree. -/
def prec (S : α → Prop) (m : Nat) : Prop := ∀ a b, S a → S b → a ≡{m}≡ b

/-- `S` is a ball. -/
def IsApprox (S : α → Prop) : Prop := ∃ c P, S = ball c P

end Approx

/-- Approximations: balls, of finite precision or singletons. -/
def Approx (α : Type _) [OFE α] := {S : α → Prop // Approx.IsApprox S}

namespace Approx
variable {α : Type _} [OFE α]

/-! ## Approximations form a CCPO -/

instance : PartialOrder (Approx α) where
  rel S T := ∀ y, T.1 y → S.1 y
  rel_refl := fun _ h => h
  rel_trans h1 h2 := fun y h => h1 y (h2 y h)
  rel_antisymm h1 h2 := Subtype.ext (funext fun y => propext ⟨h2 y, h1 y⟩)

theorem ball_self (c : α) (P) : ball c P c := fun _ _ => .rfl

theorem IsApprox.nonempty {S : α → Prop} (h : IsApprox S) : ∃ a, S a :=
  let ⟨c, P, e⟩ := h
  ⟨c, e ▸ ball_self c P⟩

theorem prec_mono {S : α → Prop} {m n} (h : prec S n) (hmn : m ≤ n) : prec S m :=
  fun a b ha hb => (h a b ha hb).le hmn

/-- An approximation is the ball around any of its elements, at its own precision. -/
theorem IsApprox.eq_ball {S : α → Prop} (h : IsApprox S) {a} (ha : S a) : S = ball a (prec S) := by
  obtain ⟨c, P, rfl⟩ := h
  have hP {m} (hm : P m) : prec (ball c P) m := fun _ _ hx hy => (hx m hm).symm.trans (hy m hm)
  funext y
  exact propext ⟨fun hy m hm => hm a y ha hy,
    fun hy m hm => (hP hm c a (ball_self c P) ha).trans (hy m (hP hm))⟩

/-- A point of an approximation. -/
noncomputable def get (S : Approx α) : α := Classical.choose S.2.nonempty

theorem get_mem (S : Approx α) : S.1 (get S) := Classical.choose_spec S.2.nonempty

/-- Points of two elements of a chain agree at any level both are precise at. -/
theorem chain_dist {c : Approx α → Prop} (hc : chain c) {S T : Approx α} (hS : c S) (hT : c T)
    {a b : α} (ha : S.1 a) (hb : T.1 b) {m} (hSm : prec S.1 m) (hTm : prec T.1 m) : a ≡{m}≡ b :=
  (hc S T hS hT).elim (fun h => hSm a b ha (h b hb)) (fun h => hTm a b (h a ha) hb)

/-- The intersection of a chain: its sup. -/
def inter (c : Approx α → Prop) : α → Prop := fun y => ∀ S, c S → S.1 y

/-- The levels some element of `c` is precise at. -/
def precs (c : Approx α → Prop) (m : Nat) : Prop := ∃ S, c S ∧ prec S.1 m

/-- If `x` is in every element of `c`, their intersection is `ball x (precs c)`. -/
theorem inter_eq_ball {c : Approx α → Prop} {x : α} (hx : ∀ S, c S → S.1 x) :
    inter c = ball x (precs c) := by
  funext y
  refine propext ⟨fun hy m ⟨S, hS, hm⟩ => hm x y (hx S hS) (hy S hS), fun hy S hS => ?_⟩
  rw [S.2.eq_ball (hx S hS)]
  exact fun m hm => hy m ⟨S, hS, hm⟩

/-- A downward-closed set of levels that is not all of them is the set below some `K`. -/
theorem exists_bound {P : Nat → Prop} (hP : ∀ {m n}, m ≤ n → P n → P m) {k} (hk : ¬ P k) :
    ∃ K, ∀ m, P m ↔ m < K := by
  induction k with
  | zero => exact ⟨0, fun m => by grind⟩
  | succ k ih =>
    by_cases h : P k
    · exact ⟨k + 1, fun m => by grind⟩
    · exact ih h

section CCPO
variable [IsCOFE α] [Inhabited α]

/-- Every chain has a point in all of its elements. -/
theorem exists_common {c : Approx α → Prop} (hc : chain c) : ∃ x, ∀ S, c S → S.1 x := by
  -- At each level `m` some element is precise at, pick such an element and a point `p m` of it.
  let S {m} (h : precs c m) : Approx α := Classical.choose h
  have hS {m} (h : precs c m) : c (S h) ∧ prec (S h).1 m := Classical.choose_spec h
  let p {m} (h : precs c m) := get (S h)
  have agree {m n} (hmn : m ≤ n) (hm : precs c m) (hn : precs c n) : p hn ≡{m}≡ p hm :=
    chain_dist hc (hS hn).1 (hS hm).1 (get_mem _) (get_mem _) (prec_mono (hS hn).2 hmn) (hS hm).2
  -- It suffices to agree with each `p m` at level `m`.
  suffices ∃ x, ∀ m (h : precs c m), p h ≡{m}≡ x by
    obtain ⟨x, hx⟩ := this
    refine ⟨x, fun T hT => ?_⟩
    obtain ⟨t, ht⟩ := T.2.nonempty
    rw [T.2.eq_ball ht]
    intro m hm
    have h : precs c m := ⟨T, hT, hm⟩
    exact (chain_dist hc hT (hS h).1 ht (get_mem _) hm (hS h).2).trans (hx m h)
  by_cases hall : ∀ m, precs c m
  · -- Precise at every level: take the limit.
    let ch : Chain α := ⟨fun n => p (hall n), fun hni => agree hni _ _⟩
    exact ⟨COFE.compl ch, fun m _ => (COFE.conv_compl (c := ch) (n := m)).symm⟩
  · -- Precise below some `K`: take the point at level `K - 1`, if any.
    obtain ⟨k, hk⟩ := Classical.not_forall.mp hall
    obtain ⟨K, hK⟩ := exists_bound (fun hmn ⟨S, hS, hn⟩ => ⟨S, hS, prec_mono hn hmn⟩) hk
    match K with
    | 0 => exact ⟨default, fun m h => by grind⟩
    | j + 1 => exact ⟨p ((hK j).2 (by omega)), fun m h => (agree (by grind) h _).symm⟩

instance : CCPO (Approx α) where
  has_csup {c} hc :=
    let ⟨x, hx⟩ := exists_common hc
    ⟨⟨inter c, x, precs c, inter_eq_ball hx⟩, fun _ =>
      ⟨fun h y hy S hS => h S hS y hy, fun h S hS y hy => h y hy S hS⟩⟩

end CCPO

/-! ## Hulls -/

section Hull
variable [Inhabited α]

/-- The smallest ball containing `T`, or everything when `T` is empty. -/
def hull (T : α → Prop) : Approx α :=
  ⟨fun z => ∀ m, prec T m → ∀ a, T a → a ≡{m}≡ z, by
    by_cases hne : ∃ a, T a
    · obtain ⟨a, ha⟩ := hne
      refine ⟨a, prec T, funext fun z => propext ⟨fun h m hm => h m hm a ha, ?_⟩⟩
      exact fun h m hm b hb => (hm b a hb ha).trans (h m hm)
    · exact ⟨default, fun _ => False, funext fun _ =>
        propext ⟨fun _ _ h => h.elim, fun _ _ _ a ha => (hne ⟨a, ha⟩).elim⟩⟩⟩

theorem mem_hull {T : α → Prop} {a : α} (ha : T a) : (hull T).1 a :=
  fun _ hm _ hb => hm _ _ hb ha

theorem prec_hull {T : α → Prop} {n : Nat} (hT : prec T n) (hne : ∃ a, T a) :
    prec (hull T).1 n :=
  let ⟨a, ha⟩ := hne
  fun _ _ hy hz => (hy n hT a ha).symm.trans (hz n hT a ha)

/-- `hull` is monotone on nonempty sets. -/
theorem hull_mono {T T' : α → Prop} (h : ∀ a, T' a → T a) (hne : ∃ a, T' a) :
    ∀ z, (hull T').1 z → (hull T).1 z :=
  let ⟨b, hb⟩ := hne
  fun _ hz m hm a ha =>
    (hm a b ha (h b hb)).trans (hz m (fun x y hx hy => hm x y (h x hx) (h y hy)) b hb)

end Hull

/-! ## Approximations of points

Balls approximate the points they contain; the best approximation of a set is its hull. -/

section Balls
variable [Inhabited α]
open PointwiseLifting (rel all)
open Approximation PointwiseLifting₂

noncomputable instance : Approximation (Approx α) α where
  mem S x := S.1 x
  hull := hull
  get := get
  mem_hull := mem_hull
  mem_get := get_mem
  hull_mono h hne := hull_mono h hne

/-- `bind₂`, `mem` and `get` on balls of `α`. -/
local notation "bindB" => bind₂ (D := Approx α) (X := α)
local notation "memB" => Approximation.mem (D := Approx α) (X := α)
local notation "getB" => Approximation.get (D := Approx α) (X := α)

/-- Balls are ordered by information: a more precise ball approximates less. -/
theorem le_iff_ext (S S' : Approx α) : S ⊑ S' ↔ Approximation.ext α S' S := .rfl

/-- The hull of a single point reads back as that point. -/
theorem get_hull {T : α → Prop} {x : α} (hx : T x) (hT : ∀ y, T y → y = x) :
    get (hull T) = x := by
  refine (OFE.eq_dist'.2 fun n => ?_).symm
  exact get_mem (hull T) n (fun a b ha hb => (hT a ha).trans (hT b hb).symm ▸ .rfl) x hx

variable {PD PX : Type _} [PointwiseLifting (Approx α) PD] [PointwiseLifting α PX]
  [PointwiseLifting₂ (Approx α) α PD PX]

/-- Every body gives a monotone `bind₂ · k`. -/
theorem bind₂_mono_approx [PartialOrder PD] [PointwiseLiftingLe (Approx α) PD] {k : PX → PX} :
    monotone fun S : PD => bindB S k :=
  bind₂_mono_info le_iff_ext

/-! ### Reading the fixpoint back -/

section ReadBack
variable [OFE PX] [PointwiseLiftingDist α PX]

/-- For a contractive body, the fixpoint of `bind₂ · k` is a single function, so `k` sends it to a
single value, and its value is a fixpoint of `k`. -/
theorem bind₂_get_approx (k : PX → PX) [Contractive k] {S : PD}
    (hS : S = bindB S k) : map₂ getB S = k (map₂ getB S) := by
  have dist {n} {a b : PX} : a ≡{n}≡ b ↔ rel (fun x y : α => x ≡{n}≡ y) a b :=
    PointwiseLiftingDist.dist_iff
  -- Every point of `S` is precise at every level, by strong induction.
  have hprec n : all (fun d : Approx α => prec d.1 n) S := by
    induction n using Nat.strongRecOn with
    | ind n ih =>
      rw [hS]
      refine all_hull₂ (Q := fun x y => x ≡{n}≡ y)
        (fun T hT ⟨x, hx⟩ => prec_hull (fun _ _ ha hb => hT _ _ ha hb) ⟨x, hx⟩) ?_
        (bind₂_nonempty (D := Approx α) (X := α) S k)
      rintro _ _ ⟨g, hg, rfl⟩ ⟨g', hg', rfl⟩
      refine dist.1 (Contractive.distLater_dist fun m hm => dist.2 ?_)
      refine PointwiseLifting.rel_mono (fun x y ⟨d, ⟨hp, hx⟩, hy⟩ => hp x y hx hy)
        (rel₂_rel (rel₂_all (ih m hm) hg) hg')
  -- So `S` approximates only `get ∘ S`.
  refine get_fix (R := (· = ·)) (fun T x hx hT => get_hull hx hT) hS fun g hg => ?_
  have hget : rel₂ memB S (map₂ getB S : PX) := rel₂_map₂ (mem_get (D := Approx α) (X := α)) S
  rw [OFE.eq_dist'.2 fun n => dist.2 <| PointwiseLifting.rel_mono
    (fun x y ⟨d, ⟨hp, hx⟩, hy⟩ => hp x y hx hy) (rel₂_rel (rel₂_all (hprec n) hg) hget)]
  exact PointwiseLifting.rel_eq _

/-- The fixpoint of `bind₂ · k`, for a contractive `k`, read back: its points are a fixpoint of
`k`. -/
theorem IsFix.get_approx [CCPO PD] {k : PX → PX}
    (hk : Contractive k) {S : PD} (h : IsFix (fun S => bindB S k) S) :
    map₂ getB S = k (map₂ getB S) :=
  bind₂_get_approx k h.unfold

end ReadBack

end Balls

/-- A fixpoint of a contractive `G` is its Banach fixpoint, whatever the default point. -/
theorem eq_fixpoint [IsCOFE α] [Inhabited α] (G : α → α) [Contractive G] {x : α}
    (h : x = G x) : x = fixpoint G :=
  fixpoint_unique (f := G.toContractiveHom) h

end Approx

end Iris
