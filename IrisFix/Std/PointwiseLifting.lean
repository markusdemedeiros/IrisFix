/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import IrisFix.Std.Order
import all Init.Internal.Order.Basic

/-! # Pointwise liftings

`PointwiseLifting B Pred` says that `Pred` is a power of `B`, curried: `B` itself, or `∀ x, β x`
for pointwise liftings `β x` of `B`. It lifts both kinds of structure on `B`: functions compute
pointwise (`map`, `zip`), and relations quantify over the points (`rel`). The laws say the two
agree. At concrete types, all of them unfold to the plain curried statements.

A structure on `B` lifts to `Pred` through `map`, `zip` and `rel`: `all C a` is `C` at every point,
`PointwiseLiftingLim` says that `all` preserves limits, and the order and meet of the BI lift as
`rel` and `zip` of the ones on `PROP`. A class that does not name its base, such as `INe`, lifts by
its own `Pi` instances instead: instance search cannot find the base `B` from `Pred` alone, since
every `Pred` is also a lifting of itself. -/

@[expose] public section

namespace Iris
open Lean.Order

/-- `Pred` is a power of `B`, curried. -/
class PointwiseLifting (B : Type _) (Pred : Type _) where
  map : (B → B) → Pred → Pred
  zip : (B → B → B) → Pred → Pred → Pred
  rel : (B → B → Prop) → Pred → Pred → Prop
  rel_mono {R S : B → B → Prop} (h : ∀ x y, R x y → S x y) {a b : Pred} : rel R a b → rel S a b
  rel_and {R S : B → B → Prop} {a b : Pred} :
    rel R a b → rel S a b → rel (fun x y => R x y ∧ S x y) a b
  rel_forall {R : B → B → Prop} (h : ∀ x y, R x y) (a b : Pred) : rel R a b
  rel_eq (a : Pred) : rel (· = ·) a a
  rel_map {R : B → B → Prop} {f g : B → B} {a b : Pred} :
    rel R (map f a) (map g b) ↔ rel (fun x y => R (f x) (g y)) a b
  map_id (a : Pred) : map id a = a
  map_const {c : B} {a b : Pred} : map (fun _ => c) a = map (fun _ => c) b
  rel_zip_l {R : B → B → Prop} {f : B → B → B} (h : ∀ x y, R (f x y) x) (a b : Pred) :
    rel R (zip f a b) a
  rel_zip_r {R : B → B → Prop} {f : B → B → B} (h : ∀ x y, R (f x y) y) (a b : Pred) :
    rel R (zip f a b) b

/-- The order of `Pred` is the order of `B`, at every point. -/
class PointwiseLiftingLe (B : Type _) (Pred : Type _) [PartialOrder B] [PartialOrder Pred]
    [PointwiseLifting B Pred] : Prop where
  le_iff {a b : Pred} : a ⊑ b ↔ PointwiseLifting.rel (fun x y : B => x ⊑ y) a b

namespace PointwiseLifting

instance instBase {B : Type _} : PointwiseLifting B B where
  map f := f
  zip f := f
  rel R := R
  rel_mono h _ _ := h _ _
  rel_and := And.intro
  rel_forall h := h
  rel_eq _ := rfl
  rel_map := .rfl
  map_id _ := rfl
  map_const := rfl
  rel_zip_l h := h
  rel_zip_r h := h

instance instPi {B : Type _} {ι : Type _} {β : ι → Type _} [∀ i, PointwiseLifting B (β i)] :
    PointwiseLifting B (∀ i, β i) where
  map f a i := map f (a i)
  zip f a b i := zip f (a i) (b i)
  rel R a b := ∀ i, rel R (a i) (b i)
  rel_mono h _ _ hab i := rel_mono h (hab i)
  rel_and hR hS i := rel_and (hR i) (hS i)
  rel_forall h a b i := rel_forall h (a i) (b i)
  rel_eq a i := rel_eq (a i)
  rel_map := forall_congr' fun _ => rel_map
  map_id a := funext fun i => map_id (a i)
  map_const := funext fun _ => map_const
  rel_zip_l h a b i := rel_zip_l h (a i) (b i)
  rel_zip_r h a b i := rel_zip_r h (a i) (b i)

instance PointwiseLiftingLe.instBase {B : Type _} [PartialOrder B] : PointwiseLiftingLe B B where
  le_iff := .rfl

instance PointwiseLiftingLe.instPi {B : Type _} [PartialOrder B] {ι : Type _} {β : ι → Type _}
    [∀ i, PartialOrder (β i)] [∀ i, PointwiseLifting B (β i)] [∀ i, PointwiseLiftingLe B (β i)] :
    PointwiseLiftingLe B (∀ i, β i) where
  le_iff := forall_congr' fun _ => PointwiseLiftingLe.le_iff

section Laws
variable {B Pred : Type _} [PointwiseLifting B Pred]

/-- On the diagonal, `rel` only sees equal points. -/
theorem rel_diag {R S : B → B → Prop} (h : ∀ x, R x x → S x x) {a : Pred} (hR : rel R a a) :
    rel S a a :=
  rel_mono (fun _ _ ⟨hxy, e⟩ => by subst e; exact h _ hxy) (rel_and hR (rel_eq a))

/-- `C` holds at every point of `a`. -/
def all (C : B → Prop) (a : Pred) : Prop := rel (fun x _ => C x) a a

/-- On the diagonal, a relation is a property of the points. -/
theorem rel_iff_all {R : B → B → Prop} {a : Pred} : rel R a a ↔ all (fun x => R x x) a :=
  ⟨rel_diag (S := fun x _ => R x x) fun _ h => h, rel_diag (R := fun x _ => R x x) fun _ h => h⟩

theorem all_imp {C D : B → Prop} (h : ∀ x, C x → D x) {a : Pred} : all C a → all D a :=
  rel_mono fun x _ => h x

theorem all_congr {C D : B → Prop} (h : ∀ x, C x ↔ D x) {a : Pred} : all C a ↔ all D a :=
  ⟨all_imp fun x => (h x).1, all_imp fun x => (h x).2⟩

theorem all_and {C D : B → Prop} {a : Pred} : all C a → all D a → all (fun x => C x ∧ D x) a :=
  rel_and

theorem all_forall {C : B → Prop} (h : ∀ x, C x) (a : Pred) : all C a :=
  rel_forall (fun x _ => h x) a a

/-- A constant family has the property of its constant. -/
theorem all_const {C : B → Prop} {c : B} (hc : C c) (a : Pred) : all C (map (fun _ => c) a) :=
  (rel_map (R := fun x _ => C x)).2 (rel_forall (fun _ _ => hc) a a)

variable [PartialOrder B] [PartialOrder Pred] [PointwiseLiftingLe B Pred]
open Iris.PointwiseLiftingLe (le_iff)

theorem map_mono {m : B → B} (hm : monotone m) : monotone (map (Pred := Pred) m) :=
  fun _ _ hab => (le_iff (B := B)).2 <| rel_map.2 <| rel_mono hm ((le_iff (B := B)).1 hab)

theorem le_map_iff {m : B → B} {a : Pred} : a ⊑ map m a ↔ all (fun x => x ⊑ m x) a := by
  have e := rel_map (R := fun x y : B => x ⊑ y) (f := id) (g := m) (a := a) (b := a)
  rw [map_id] at e
  rw [le_iff (B := B), e]
  exact rel_iff_all

theorem map_le_iff {m : B → B} {a : Pred} : map m a ⊑ a ↔ all (fun x => m x ⊑ x) a := by
  have e := rel_map (R := fun x y : B => x ⊑ y) (f := m) (g := id) (a := a) (b := a)
  rw [map_id] at e
  rw [le_iff (B := B), e]
  exact rel_iff_all

/-- `C` at every point is a postfixpoint of `map m`, for `C x ↔ x ⊑ m x`. -/
theorem all_le {C : B → Prop} {m : B → B} (h : ∀ x, C x ↔ x ⊑ m x) (a : Pred) :
    all C a ↔ a ⊑ map m a :=
  (all_congr h).trans le_map_iff.symm

end Laws

section Fix
variable {B Pred : Type _} [PointwiseLifting B Pred] [PartialOrder B] [CCPO Pred]
  [PointwiseLiftingLe B Pred]

/-- `C` at every point of a fixpoint, for `C x ↔ x ⊑ m x` and `m` below the identity there. -/
theorem _root_.Iris.IsFix.all {F : Pred → Pred} {fn : Pred} (hfix : IsFix F fn) (hF : monotone F)
    {C : B → Prop} {m : B → B} (hm : monotone m) (hC : ∀ x, C x ↔ x ⊑ m x)
    (hle : all (fun x => m x ⊑ x) fn) (h : all C (F (map m fn))) : all C fn :=
  (all_le hC _).2 <| hfix.le_map hF (map_mono hm) (map_le_iff.2 hle) ((all_le hC _).1 h)

end Fix

end PointwiseLifting

open PointwiseLifting in
/-- `all` preserves limits. -/
class PointwiseLiftingLim (B : Type _) [COFE B] (Pred : Type _) [COFE Pred]
    [PointwiseLifting B Pred] : Prop where
  all_lim {C : B → Prop} : LimitPreserving C → LimitPreserving (all C : Pred → Prop)

instance PointwiseLiftingLim.instBase {B : Type _} [COFE B] : PointwiseLiftingLim B B where
  all_lim h := h

instance PointwiseLiftingLim.instPi {B : Type _} [COFE B] {ι : Type _} {β : ι → Type _}
    [∀ i, COFE (β i)] [∀ i, PointwiseLifting B (β i)] [∀ i, PointwiseLiftingLim B (β i)] :
    PointwiseLiftingLim B (∀ i, β i) where
  all_lim h := ⟨fun c hc i => (PointwiseLiftingLim.all_lim (Pred := β i) h).compl
    (c.map (OFE.applyHom i)) fun n => hc n i⟩

end Iris
