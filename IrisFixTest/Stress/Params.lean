/-
Stress tests: parameter shapes for `ifix` / `icofix`.
-/
module

public import Iris.BI
public import IrisFix.ProofMode.Lib.Fixpoint

@[expose] public section
open Iris BI OFE

set_option linter.iris.style.whitespace false

namespace IrisTest.Stress.Params

local bi PROP

variable {PROP : Type _} [BI PROP]

/-! ## Zero parameters -/

ifix z0 : PROP := iprop% ▷ z0

example : z0 (PROP := PROP) = z0.pre z0 := z0.unfold
example (Φ : PROP) : ⊢ □ (z0.pre Φ -∗ Φ) -∗ z0 -∗ Φ := z0.iter Φ
example (Φ : PROP) : ⊢ □ (z0.pre iprop(Φ ∧ z0) -∗ Φ) -∗ z0 -∗ Φ := z0.ind Φ
example (Φ W : PROP) (hW : iprop(Φ ∧ z0.pre W) ⊢ W) : ⊢ □ (z0.pre W -∗ Φ) -∗ z0 -∗ Φ :=
  z0.ind_wf Φ W hW
example (G : PROP → PROP) (g : PROP) (hg : G g ⊢ g) : ⊢ □ (∀ Φ, z0.pre Φ -∗ G Φ) -∗ z0 -∗ g :=
  z0.strong_mono G g hg
example [BIAffine PROP] : Affine (z0 (PROP := PROP)) := inferInstance
example : Persistent (z0 (PROP := PROP)) := inferInstance

icofix zc0 : PROP := iprop% ▷ zc0

example : zc0 (PROP := PROP) = zc0.pre zc0 := zc0.unfold
example (Φ : PROP) : ⊢ □ (Φ -∗ zc0.pre Φ) -∗ Φ -∗ zc0 := zc0.coiter Φ
example (Φ : PROP) : ⊢ □ (Φ -∗ zc0.pre iprop(Φ ∨ zc0)) -∗ Φ -∗ zc0 := zc0.coind Φ
example (Φ W : PROP) (hW : W ⊢ iprop(Φ ∨ zc0.pre W)) : ⊢ □ (Φ -∗ zc0.pre W) -∗ Φ -∗ zc0 :=
  zc0.paco Φ W hW
example : Absorbing (zc0 (PROP := PROP)) := inferInstance

/-! ## One parameter, passed on unchanged -/

ifix f1 (P : PROP) : PROP := iprop% P ∗ ▷ f1 P

example (P : PROP) : f1 P = f1.pre f1 P := f1.unfold P
example (Φ : PROP → PROP) : ⊢ □ (∀ P, f1.pre Φ P -∗ Φ P) -∗ ∀ P, f1 P -∗ Φ P := f1.iter Φ
example [BIAffine PROP] (P : PROP) : Affine (f1 P) := inferInstance

/-! ## Parameters passed on unchanged and changed, in every order -/

-- Unchanged last.
ifix fl (n : Nat) (P : PROP) : PROP := iprop% P ∨ ▷ fl (n + 1) P

example (n : Nat) (P : PROP) : fl n P = fl.pre fl n P := fl.unfold n P
example (Φ : Nat → PROP → PROP) :
    ⊢ □ (∀ n P, iprop(P ∨ ▷ Φ (n + 1) P) -∗ Φ n P) -∗ ∀ n P, fl n P -∗ Φ n P :=
  fl.iter Φ
example (Φ : Nat → PROP → PROP) :
    ⊢ □ (∀ n P, fl.pre (fun n P => iprop(Φ n P ∧ fl n P)) n P -∗ Φ n P) -∗
      ∀ n P, fl n P -∗ Φ n P :=
  fl.ind Φ
-- An instance that needs an instance of a fixed (section variable) parameter.
section
variable (P : PROP) [Persistent P] [Absorbing P]
ifix flP (n : Nat) : PROP := iprop% P ∨ ▷ flP (n + 1)
example (n : Nat) : Persistent (flP P n) := inferInstance
end
example [BIAffine PROP] (P : PROP) (n : Nat) : Affine (fl n P) := inferInstance

icofix cfl (n : Nat) (P : PROP) : PROP := iprop% P ∗ ▷ cfl (n + 1) P

example (n : Nat) (P : PROP) : cfl n P = cfl.pre cfl n P := cfl.unfold n P
example (Φ : Nat → PROP → PROP) :
    ⊢ □ (∀ n P, Φ n P -∗ cfl.pre Φ n P) -∗ ∀ n P, Φ n P -∗ cfl n P := cfl.coiter Φ

-- Interleaved: unchanged and changed, alternating.
ifix il (a : Nat) (x : Nat) (b : Bool) (y : Bool) (P : PROP) (z : Nat) : PROP :=
  iprop(P ∨ ▷ il a (x + 1) b (!y) P (z + a))

example (a x : Nat) (b y : Bool) (P : PROP) (z : Nat) :
    il a x b y P z = il.pre il a x b y P z :=
  il.unfold a x b y P z
example (Φ : Nat → Nat → Bool → Bool → PROP → Nat → PROP) :
    ⊢ □ (∀ a x b y P z, il.pre Φ a x b y P z -∗ Φ a x b y P z) -∗
      ∀ a x b y P z, il a x b y P z -∗ Φ a x b y P z :=
  il.iter Φ
example (Φ W : Nat → Nat → Bool → Bool → PROP → Nat → PROP)
    (hW : ∀ a x b y P z, iprop(Φ a x b y P z ∧ il.pre W a x b y P z) ⊢ W a x b y P z) :
    ⊢ □ (∀ a x b y P z, il.pre W a x b y P z -∗ Φ a x b y P z) -∗
      ∀ a x b y P z, il a x b y P z -∗ Φ a x b y P z :=
  il.ind_wf Φ W hW
example (G : (Nat → Nat → Bool → Bool → PROP → Nat → PROP) → Nat → Nat → Bool → Bool → PROP → Nat →
      PROP)
    (g : Nat → Nat → Bool → Bool → PROP → Nat → PROP)
    (hg : ∀ a x b y P z, G g a x b y P z ⊢ g a x b y P z) :
    ⊢ □ (∀ Φ a x b y P z, il.pre Φ a x b y P z -∗ G Φ a x b y P z) -∗
      ∀ a x b y P z, il a x b y P z -∗ g a x b y P z :=
  il.strong_mono G g hg

-- Interleaved: changed and unchanged, alternating, greatest fixpoint.
icofix il2 (x : Nat) (a : Nat) (y : Bool) (b : Bool) : PROP :=
  iprop(⌜a = x⌝ ∗ ▷ il2 (x + 1) a (!y) b)

example (x a : Nat) (y b : Bool) : il2 (PROP := PROP) x a y b = il2.pre il2 x a y b :=
  il2.unfold x a y b
example (Φ W : Nat → Nat → Bool → Bool → PROP)
    (hW : ∀ x a y b, W x a y b ⊢ iprop(Φ x a y b ∨ il2.pre W x a y b)) :
    ⊢ □ (∀ x a y b, Φ x a y b -∗ il2.pre W x a y b) -∗ ∀ x a y b, Φ x a y b -∗ il2 x a y b :=
  il2.paco Φ W hW
example (a : Nat) (b : Bool) (x : Nat) (y : Bool) : Absorbing (il2 (PROP := PROP) x a y b) := inferInstance

-- Eight parameters, four of them passed on unchanged, interleaved.
ifix big (a : Nat) (P : PROP) (b : Bool) (Q : PROP) (c : Nat) (R : PROP) (d : Bool) (S : PROP) :
    PROP :=
  iprop(P ∗ Q ∗ R ∗ S ∨ ▷ big (a + 1) P (!b) Q (c + 1) R (!d) S)

example (Φ : Nat → PROP → Bool → PROP → Nat → PROP → Bool → PROP → PROP) :
    ⊢ □ (∀ a P b Q c R d S, big.pre Φ a P b Q c R d S -∗ Φ a P b Q c R d S) -∗
      ∀ a P b Q c R d S, big a P b Q c R d S -∗ Φ a P b Q c R d S :=
  big.iter Φ

-- A parameter swapped with another varies.
ifix sw2 (a b : Nat) : PROP := iprop% ⌜a = b⌝ ∨ ▷ sw2 b a
example (Φ : Nat → Nat → PROP) :
    ⊢ □ (∀ a b, sw2.pre Φ a b -∗ Φ a b) -∗ ∀ a b, sw2 a b -∗ Φ a b := sw2.iter Φ

-- A bare recursive reference keeps every argument varying.
ifix bare (n : Nat) (P : PROP) : PROP := let next := bare; iprop(P ∨ ▷ next (n + 1) P)
example (Φ : Nat → PROP → PROP) :
    ⊢ □ (∀ n P, bare.pre Φ n P -∗ Φ n P) -∗ ∀ n P, bare n P -∗ Φ n P := bare.iter Φ

/-! ## Implicit, strict-implicit, instance-implicit binders -/

-- Implicit varying (its name is not in the result type).
ifix imf {P : PROP} (n : Nat) : PROP := iprop% P ∨ imf (P := P) (n + 1)
example (Φ : PROP → Nat → PROP) :
    ⊢ □ (∀ P n, imf.pre (fun {P} => Φ P) (P := P) n -∗ Φ P n) -∗ ∀ P n, imf (P := P) n -∗ Φ P n := imf.iter Φ

-- Implicit varying: the motive is `Φ : Nat → PROP` (`pre` still takes `{n : Nat} → PROP`).
ifix imv {n : Nat} : PROP := iprop% ⌜n = 0⌝ ∨ ▷ imv (n := n + 1)
example (n : Nat) : imv (PROP := PROP) (n := n) = imv.pre (fun {m} => imv (n := m)) (n := n) :=
  imv.unfold n
example (Φ : Nat → PROP) :
    ⊢ □ (∀ n, imv.pre (fun {m} => Φ m) (n := n) -∗ Φ n) -∗ ∀ n, imv (n := n) -∗ Φ n :=
  imv.iter Φ
example (n : Nat) : Persistent (imv (PROP := PROP) (n := n)) := inferInstance

-- Strict implicit varying.
ifix simv ⦃n : Nat⦄ : PROP := iprop% ⌜n = 0⌝ ∨ ▷ simv (n := n + 1)
example (n : Nat) : Persistent (simv (PROP := PROP) (n := n)) := inferInstance

-- Implicit and instance-implicit, passed on unchanged, after another parameter.
ifix late (n : Nat) {α : Type} [Inhabited α] : PROP := iprop% ⌜n = 0⌝ ∨ ▷ late (α := α) (n + 1)
example (Φ : Nat → {α : Type} → [Inhabited α] → PROP) :
    ⊢ □ (∀ n α (_ : Inhabited α), late.pre Φ n (α := α) -∗ Φ n (α := α)) -∗
      ∀ n α (_ : Inhabited α), late n (α := α) -∗ Φ n (α := α) := late.iter Φ
example [BIAffine PROP] {α : Type} [Inhabited α] (n : Nat) : Affine (late (PROP := PROP) n (α := α)) :=
  inferInstance

-- Instance-implicit varying (the instance varies with `b`).
ifix instv (b : Bool) [Decidable (b = true)] : PROP := iprop% ⌜b = true⌝ ∨ instv (!b)
example [BIAffine PROP] (b : Bool) : Persistent (instv (PROP := PROP) b) := inferInstance

/-! ## Dependent parameters -/

-- A changing parameter depends on an unchanged one.
ifix dep1 (n : Nat) (i : Fin (n + 1)) : PROP := iprop% ⌜i.val = 0⌝ ∨ ▷ dep1 n 0
example (Φ : (n : Nat) → Fin (n + 1) → PROP) :
    ⊢ □ (∀ n i, dep1.pre Φ n i -∗ Φ n i) -∗ ∀ n i, dep1 n i -∗ Φ n i := dep1.iter Φ

-- A changing parameter depends on a changing one.
ifix dep2 (n : Nat) (i : Fin (n + 1)) : PROP := iprop% ⌜i.val = 0⌝ ∨ ▷ dep2 (n + 1) 0
example (Φ : (n : Nat) → Fin (n + 1) → PROP) :
    ⊢ □ (∀ n i, dep2.pre (fun n i => iprop(Φ n i ∧ dep2 n i)) n i -∗ Φ n i) -∗
      ∀ n i, dep2 n i -∗ Φ n i := dep2.ind Φ

-- Unchanged between two changing ones, the later changing one depending on it.
ifix dep5 (x : Nat) (n : Nat) (v : Fin (n + 1)) : PROP := iprop% ⌜v.val = x⌝ ∨ ▷ dep5 (x + 1) n 0
example (x n : Nat) (v : Fin (n + 1)) :
    dep5 (PROP := PROP) x n v = dep5.pre dep5 x n v := dep5.unfold x n v
example (Φ : Nat → (n : Nat) → Fin (n + 1) → PROP) :
    ⊢ □ (∀ x n v, iprop(⌜v.val = x⌝ ∨ ▷ Φ (x + 1) n 0) -∗ Φ x n v) -∗
      ∀ x n v, dep5 x n v -∗ Φ x n v :=
  dep5.iter Φ
example [BIAffine PROP] (x n : Nat) (v : Fin (n + 1)) : Affine (dep5 (PROP := PROP) x n v) :=
  inferInstance

-- Unchanged parameters whose types depend on each other, before a changing one.
ifix dep4 (n : Nat) (v : Fin (n + 1)) (k : Nat) : PROP := iprop% ⌜v.val = k⌝ ∨ ▷ dep4 n v (k + 1)
example (Φ : (n : Nat) → Fin (n + 1) → Nat → PROP) :
    ⊢ □ (∀ n v k, dep4.pre Φ n v k -∗ Φ n v k) -∗ ∀ n v k, dep4 n v k -∗ Φ n v k := dep4.iter Φ

-- Limitation: an auto-bound implicit is a parameter of the definition, not of the recursive call,
-- so the call cannot name it, `(n := n)`.
/--
error: Invalid argument name `n` for function

Hint: Perhaps you meant one of the following parameter names:
  • `_i`: n̵_̲i̲
  • `P`: n̵P̲
-/
#guard_msgs in
ifix dep3 (_i : Fin (n + 1)) (P : PROP) : PROP := iprop% P ∨ ▷ dep3 (n := n) 0 P

-- Auto-bound implicit fixed, mentioned only in the type of a varying parameter.
ifix dep3' (_i : Fin (n + 1)) (P : PROP) : PROP := iprop% P ∨ ▷ dep3' 0 P
example {n : Nat} (Φ : Fin (n + 1) → PROP → PROP) :
    ⊢ □ (∀ i P, dep3'.pre Φ i P -∗ Φ i P) -∗ ∀ i P, dep3' i P -∗ Φ i P := dep3'.iter Φ

/-! ## Prop-, Type- and universe-polymorphic parameters -/

ifix propv (p : Prop) : PROP := iprop% ⌜p⌝ ∨ ▷ propv (¬p)
example (Φ : Prop → PROP) : ⊢ □ (∀ p, propv.pre Φ p -∗ Φ p) -∗ ∀ p, propv p -∗ Φ p := propv.iter Φ

-- A proof as a fixed (section variable) parameter is fine.
section
variable (n : Nat) (h : n > 0)
ifix prff (k : Nat) : PROP := iprop% ⌜(⟨n, h⟩ : {m : Nat // m > 0}).1 = k⌝ ∨ ▷ prff (k + 1)
example (Φ : Nat → PROP) :
    ⊢ □ (∀ k, prff.pre n h Φ k -∗ Φ k) -∗ ∀ k, prff n h k -∗ Φ k := prff.iter n h Φ
end

ifix typev (α : Type) : PROP := iprop% ⌜Nonempty α⌝ ∨ ▷ typev (List α)
example (α : Type) : Persistent (typev (PROP := PROP) α) := inferInstance

ifix typef (α : Type) (xs : List α) : PROP :=
  iprop(⌜xs = []⌝ ∨ ∃ x ys, ⌜xs = x :: ys⌝ ∗ typef α ys)
example (Φ : (α : Type) → List α → PROP) :
    ⊢ □ (∀ α xs, typef.pre Φ α xs -∗ Φ α xs) -∗ ∀ α xs, typef α xs -∗ Φ α xs := typef.iter Φ

universe u w

ifix upoly {α : Type u} (xs : List α) : PROP :=
  iprop(⌜xs = []⌝ ∨ ∃ x ys, ⌜xs = x :: ys⌝ ∗ upoly ys)
example (Φ : (α : Type u) → List α → PROP) :
    ⊢ □ (∀ α xs, upoly.pre (fun {α} => Φ α) (α := α) xs -∗ Φ α xs) -∗ ∀ α xs, upoly (α := α) xs -∗ Φ α xs :=
  upoly.iter Φ

-- A varying `Sort`.
ifix uvary (α : Sort u) : PROP := iprop% ⌜Nonempty α⌝ ∨ ▷ uvary (α → α)
example (Φ : Sort u → PROP) :
    ⊢ □ (∀ (α : Sort u), uvary.pre Φ α -∗ Φ α) -∗ ∀ (α : Sort u), uvary α -∗ Φ α := uvary.iter Φ

-- Limitation: `PROP'` and `[BI PROP']` are fixed, but `{α : Sort w}` varies (the `Sort` limitation).
/--
error: failed to synthesize
  PointwiseLifting PROP' ({α : Sort w} → (α → Nat) → α → Nat → PROP')

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
---
warning: unused `partial_fixpoint`, function is not recursive
-/
#guard_msgs in
ifix uu {PROP' : Type u} [BI PROP'] {α : Sort w} (f : α → Nat) (x : α) (n : Nat) : PROP' :=
  iprop(⌜f x = n⌝ ∨ ▷ uu f x (n + 1))

-- Limitation: an explicit BI parameter makes the result type depend on a parameter.
/--
error: the result type
  PROP'
depends on the parameters
---
warning: unused `partial_fixpoint`, function is not recursive
-/
#guard_msgs in
ifix uuE (PROP' : Type u) [BI PROP'] (n : Nat) : PROP' := iprop% ⌜0 = n⌝ ∨ ▷ uuE PROP' (n + 1)

-- Own BI, with a fixed `Sort w` domain, as section variables.
section
variable {PROP' : Type u} [BI PROP'] {α : Sort w} (f : α → Nat) (x : α)
ifix uu' (n : Nat) : PROP' := iprop% ⌜f x = n⌝ ∨ ▷ uu' (n + 1)
/--
info: @uu'.iter : ∀ {PROP' : Type u_1} [inst : BI PROP'] {α : Sort u_2} (f : α → Nat) (x : α) (Φ : Nat → PROP'),
  ⊢ (□ ∀ n, uu'.pre f x Φ n -∗ Φ n) -∗ ∀ n, uu' f x n -∗ Φ n
-/
#guard_msgs in #check @uu'.iter
end

-- Universes only the body mentions.
ifix ub (n : Nat) : PROP := iprop% ⌜PUnit.{3} = PUnit.{3}⌝ ∨ ▷ ub (n + 1)
example (Φ : Nat → PROP) : ⊢ □ (∀ n, ub.pre Φ n -∗ Φ n) -∗ ∀ n, ub n -∗ Φ n := ub.iter Φ

-- Product and `PSigma` parameters stay one parameter.
ifix prod (p : Nat × Bool) : PROP := iprop% ⌜p.1 = 0⌝ ∨ ▷ prod (p.1 + 1, !p.2)
example (Φ : Nat × Bool → PROP) : ⊢ □ (∀ p, prod.pre Φ p -∗ Φ p) -∗ ∀ p, prod p -∗ Φ p := prod.iter Φ
ifix psig (p : (n : Nat) ×' Fin (n + 1)) : PROP := iprop% ⌜p.2.val = 0⌝ ∨ ▷ psig ⟨p.1 + 1, 0⟩
example (Φ : (n : Nat) ×' Fin (n + 1) → PROP) :
    ⊢ □ (∀ p, psig.pre Φ p -∗ Φ p) -∗ ∀ p, psig p -∗ Φ p := psig.iter Φ

/-! ## Function-typed parameters -/

ifix funv (f : Nat → Nat) (n : Nat) : PROP := iprop% ⌜f n = 0⌝ ∨ ▷ funv (f ∘ Nat.succ) n
example (Φ : (Nat → Nat) → Nat → PROP) :
    ⊢ □ (∀ f n, funv.pre Φ f n -∗ Φ f n) -∗ ∀ f n, funv f n -∗ Φ f n := funv.iter Φ

ifix funf (f : Nat → Nat) (n : Nat) : PROP := iprop% ⌜f n = 0⌝ ∨ ▷ funf f (f n)
example (Φ : (Nat → Nat) → Nat → PROP) :
    ⊢ □ (∀ f n, funf.pre Φ f n -∗ Φ f n) -∗ ∀ f n, funf f n -∗ Φ f n := funf.iter Φ

ifix hof (Q : Nat → PROP) (n : Nat) : PROP := iprop% Q n ∨ ▷ hof Q (n + 1)
example (Φ : (Nat → PROP) → Nat → PROP) :
    ⊢ □ (∀ Q n, iprop(Q n ∨ ▷ Φ Q (n + 1)) -∗ Φ Q n) -∗ ∀ Q n, hof Q n -∗ Φ Q n := hof.iter Φ

/-! ## Section variables, defaults, no type, `fun` with alternatives -/

section
variable (Q : PROP)
ifix sv (n : Nat) : PROP := iprop% Q ∨ ▷ sv (n + 1)
example (Φ : Nat → PROP) : ⊢ □ (∀ n, sv.pre Q Φ n -∗ Φ n) -∗ ∀ n, sv Q n -∗ Φ n := sv.iter Q Φ
end

-- Limitation: a definition without a type is rejected.
/-- error: ifix: the type of the fixpoint is needed -/
#guard_msgs in
ifix noty (n : Nat) := iprop% ⌜n = 0⌝ ∨ ▷ (noty (n + 1) : PROP)

ifix pm (P : PROP) : Nat → PROP := fun
  | 0 => P
  | n + 1 => iprop(▷ pm P n)
example (Φ : PROP → Nat → PROP) :
    ⊢ □ (∀ P n, pm.pre Φ P n -∗ Φ P n) -∗ ∀ P n, pm P n -∗ Φ P n := pm.iter Φ

-- Rejected: `where` declarations after the alternatives.
/-- error: ifix: the body takes no termination hints or `where` declarations -/
#guard_msgs in
ifix pmw (P : PROP) : Nat → PROP
  | 0 => P
  | n + 1 => iprop(▷ pmw (f P) n)
where f (P : PROP) : PROP := P

/-! ## Result types that are not literally `PROP` -/

abbrev MyProp (PROP : Type _) := PROP
ifix abr (n : Nat) : MyProp PROP := iprop% ⌜n = 0⌝ ∨ ▷ abr (n + 1)
example (Φ : Nat → PROP) : ⊢ □ (∀ n, abr.pre Φ n -∗ Φ n) -∗ ∀ n, abr n -∗ Φ n := abr.iter Φ

@[reducible] def RP (PROP : Type _) := PROP
ifix rdw (n : Nat) : Nat → RP PROP := fun m => iprop(⌜n = m⌝ ∨ ▷ rdw (n + 1) (m + 1))
example [BIAffine PROP] (n m : Nat) : Affine (rdw (PROP := PROP) n m) := inferInstance

-- Function-typed result: its parameters are parameters too (`m` passed on unchanged here).
ifix fres (n : Nat) : Nat → PROP := fun m => iprop(⌜n = m⌝ ∨ ▷ fres (n + 1) m)
example (n m : Nat) : fres (PROP := PROP) n m = fres.pre fres n m := fres.unfold n m
example (Φ : Nat → Nat → PROP) :
    ⊢ □ (∀ n m, fres.pre Φ n m -∗ Φ n m) -∗ ∀ n m, fres n m -∗ Φ n m := fres.iter Φ

icofix fres5 (P : PROP) : Nat → Bool → PROP := fun m b => iprop(P ∗ ▷ fres5 P (m + 1) !b)
example (P : PROP) [Absorbing P] (m : Nat) (b : Bool) : Absorbing (fres5 P m b) := inferInstance
example (Φ : PROP → Nat → Bool → PROP) :
    ⊢ □ (∀ P m b, Φ P m b -∗ iprop(P ∗ ▷ Φ P (m + 1) !b)) -∗ ∀ P m b, Φ P m b -∗ fres5 P m b :=
  fres5.coiter Φ

abbrev Pred2 (PROP : Type _) := Nat → Bool → PROP
ifix ali : Pred2 PROP := fun n b => iprop(⌜n = 0⌝ ∨ ▷ ali (n + 1) !b)
example (Φ : Nat → Bool → PROP) :
    ⊢ □ (∀ n b, ali.pre Φ n b -∗ Φ n b) -∗ ∀ n b, ali n b -∗ Φ n b := ali.iter Φ

/-! ## Many varying parameters -/

ifix m4 (a b c d : Nat) : PROP := iprop% ⌜a = 0⌝ ∨ ▷ m4 b c d a
example (Φ : Nat → Nat → Nat → Nat → PROP) :
    ⊢ □ (∀ a b c d, m4.pre Φ a b c d -∗ Φ a b c d) -∗ ∀ a b c d, m4 a b c d -∗ Φ a b c d :=
  m4.iter Φ

-- Seven varying parameters.
ifix m7 (a b c d e f g : Nat) : PROP := iprop% ⌜a = 0⌝ ∨ ▷ m7 b c d e f g a
example (Φ : Nat → Nat → Nat → Nat → Nat → Nat → Nat → PROP) :
    ⊢ □ (∀ a b c d e f g, m7.pre Φ a b c d e f g -∗ Φ a b c d e f g) -∗
      ∀ a b c d e f g, m7 a b c d e f g -∗ Φ a b c d e f g :=
  m7.iter Φ

/-! ## OFEs and `ne` -/

section
variable {α β : Type _}

-- Both varying, with OFEs: `ne`. The leading `[OFE α]` is fixed.
ifix o1 [OFE α] (x y : α) : PROP := iprop% ▷ o1 y x
example [OFE α] {n : Nat} {x x' y y' : α} (hx : x ≡{n}≡ x') (hy : y ≡{n}≡ y') :
    o1 (PROP := PROP) x y ≡{n}≡ o1 x' y' :=
  o1.ne (fun _ _ hf x x' hx y y' hy => later_ne.ne (hf y y' hy x x' hx)) x x' hx y y' hy

-- OFE and non-OFE varying, in both orders; icofix.
ifix o3 [OFE α] (x y : α) (k : Nat) : PROP := iprop% ▷ o3 y x (k + 1)
example [OFE α] {n : Nat} (k : Nat) {x x' y y' : α} (hx : x ≡{n}≡ x') (hy : y ≡{n}≡ y') :
    o3 (PROP := PROP) x y k ≡{n}≡ o3 x' y' k :=
  o3.ne (fun _ _ hf x x' hx y y' hy k => later_ne.ne (hf y y' hy x x' hx (k + 1))) x x' hx y y' hy k
ifix o4 [OFE α] (k : Nat) (x y : α) : PROP := iprop% ▷ o4 (k + 1) y x
example [OFE α] {n : Nat} (k : Nat) {x x' y y' : α} (hx : x ≡{n}≡ x') (hy : y ≡{n}≡ y') :
    o4 (PROP := PROP) k x y ≡{n}≡ o4 k x' y' :=
  o4.ne (fun _ _ hf k x x' hx y y' hy => later_ne.ne (hf (k + 1) y y' hy x x' hx)) k x x' hx y y' hy
icofix o5 [OFE α] (x y : α) : PROP := iprop% ▷ o5 y x
example [OFE α] {n : Nat} {x x' y y' : α} (hx : x ≡{n}≡ x') (hy : y ≡{n}≡ y') :
    o5 (PROP := PROP) x y ≡{n}≡ o5 x' y' :=
  o5.ne (fun _ _ hf x x' hx y y' hy => later_ne.ne (hf y y' hy x x' hx)) x x' hx y y' hy

-- Two different OFEs.
ifix o7 [OFE α] [OFE β] (f : α → α) (g : β → β) (x : α) (y : β) : PROP := iprop% ▷ o7 f g (f x) (g y)
#guard_msgs (drop info) in #check @o7.ne

-- A varying `PROP` and a varying family of `PROP`s have OFEs.
ifix o6 (P : PROP) (k : Nat) : PROP := iprop% P ∨ ▷ o6 iprop(P ∗ P) (k + 1)
#guard_msgs (drop info) in #check @o6.ne
ifix o11 (Q : Nat → PROP) : PROP := iprop% ▷ o11 (fun k => Q (k + 1))
#guard_msgs (drop info) in #check @o11.ne
ifix o12 (k : Nat) (v : Fin k → PROP) : PROP := iprop% ▷ o12 k (fun i => iprop(v i ∗ v i))
#guard_msgs (drop info) in #check @o12.ne

-- Implicit varying with an OFE.
ifix o8 [OFE α] (f : α → α) {x : α} : PROP := iprop% ▷ o8 f (x := f x)
#guard_msgs (drop info) in #check @o8.ne

-- No OFE among the varying parameters: no `ne`.
ifix o2 (k : Nat) : PROP := iprop% ▷ o2 (k + 1)
/--
error: Unknown constant `IrisTest.Stress.Params.o2.ne`
-/
#guard_msgs in #check @o2.ne

-- An OFE parameter that is fixed (a section variable): no `ne` (the spec asks for `ne` only for
-- varying ones).
section
variable (x : PROP)
ifix ofix (k : Nat) : PROP := iprop% x ∗ ▷ ofix (k + 1)
/--
error: Unknown constant `IrisTest.Stress.Params.ofix.ne`
-/
#guard_msgs in #check @ofix.ne
end
end

/-! ## Five and more varying parameters (default instance budget) -/

ifix m5 (a b c d e : Nat) : PROP := iprop% ⌜a = 0⌝ ∨ ▷ m5 b c d e a
example (Φ : Nat → Nat → Nat → Nat → Nat → PROP) :
    ⊢ □ (∀ a b c d e, m5.pre Φ a b c d e -∗ Φ a b c d e) -∗
      ∀ a b c d e, m5 a b c d e -∗ Φ a b c d e :=
  m5.iter Φ

icofix c5 (a b c d e : Nat) : PROP := iprop% ▷ c5 b c d e a
example (Φ : Nat → Nat → Nat → Nat → Nat → PROP) :
    ⊢ □ (∀ a b c d e, Φ a b c d e -∗ c5.pre Φ a b c d e) -∗
      ∀ a b c d e, Φ a b c d e -∗ c5 a b c d e :=
  c5.coiter Φ

-- Varying parameters in the result type.
ifix m5r (a : Nat) : Nat → Nat → Nat → Nat → PROP := fun b c d e =>
  iprop(⌜a = 0⌝ ∨ ▷ m5r b c d e a)
example (a b c d e : Nat) : m5r (PROP := PROP) a b c d e = m5r.pre m5r a b c d e :=
  m5r.unfold a b c d e

ifix m6 (a b c d e f : Nat) : PROP := iprop% ⌜a = 0⌝ ∨ ▷ m6 b c d e f a
example (a b c d e f : Nat) : m6 (PROP := PROP) a b c d e f = m6.pre m6 a b c d e f :=
  m6.unfold a b c d e f

/-! ## Non-recursive bodies -/

ifix nonRec (n : Nat) : PROP := iprop% ⌜n = 0⌝
example (n : Nat) : nonRec (PROP := PROP) n = nonRec.pre nonRec n := nonRec.unfold n
example (n : Nat) : Persistent (nonRec (PROP := PROP) n) := inferInstance

ifix nrf : Nat → PROP := fun n => iprop(⌜n = 0⌝)
example (n : Nat) : nrf (PROP := PROP) n = nrf.pre nrf n := nrf.unfold n

-- A body headed by a constant without a value.
axiom myAx : PROP
noncomputable ifix axBody (_n : Nat) : PROP := myAx
example (n : Nat) : axBody (PROP := PROP) n = axBody.pre axBody n := axBody.unfold n

/-! ## Optional parameters -/

-- Laws drop the `optParam`.
ifix dv (n : Nat := 0) (k : Nat) : PROP := iprop% ⌜n = k⌝ ∨ ▷ dv (n + 1) k
example (Φ : Nat → Nat → PROP) :
    ⊢ □ (∀ n k, dv.pre Φ n k -∗ Φ n k) -∗ ∀ n k, dv n k -∗ Φ n k := dv.iter Φ

/-! ## Limitations and remaining bugs -/

section
variable {α : Type _}

-- Limitation: varying parameters of type `Prop`/`Sort` (here a proof) are out of scope.
/--
error: failed to synthesize
  PointwiseLifting PROP ((n : Nat) → n > 0 → PROP)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
---
warning: unused `partial_fixpoint`, function is not recursive
-/
#guard_msgs in
ifix prfv (n : Nat) (h : n > 0) : PROP := iprop% ⌜n = 1⌝ ∨ ▷ prfv (n + 1) (Nat.succ_pos n)

-- Limitation: same, for an implicit proof parameter.
/--
error: failed to synthesize
  PointwiseLifting PROP ((n : Nat) → {h : n > 0} → PROP)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
---
warning: unused `partial_fixpoint`, function is not recursive
-/
#guard_msgs in
ifix prfi (n : Nat) {h : n > 0} : PROP := iprop% ⌜n = 1⌝ ∨ ▷ prfi (n + 1) (h := Nat.succ_pos n)

-- Limitation: same, for an autoParam (a proof) that varies.
/--
error: failed to synthesize
  PointwiseLifting PROP ((n : Nat) → autoParam (n = n) ap._auto_1 → PROP)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
---
warning: unused `partial_fixpoint`, function is not recursive
-/
#guard_msgs in
ifix ap (n : Nat) (h : n = n := by rfl) : PROP := iprop% ⌜n = 0⌝ ∨ ▷ ap (n + 1)

-- Limitation: same, for a varying parameter whose type lives in `Sort w`.
/--
error: failed to synthesize
  PointwiseLifting PROP ({β : Sort w} → (β → β) → β → PROP)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
---
warning: unused `partial_fixpoint`, function is not recursive
-/
#guard_msgs in
ifix uv {β : Sort w} (f : β → β) (x : β) : PROP := iprop% ▷ uv f (f x)

-- Limitation: no `ne` when the OFE instance is itself a varying parameter.
ifix vofe (γ : Type) [OFE γ] (x : γ) : PROP := iprop% ▷ vofe (γ × γ) (x, x)
/-- error: Unknown constant `IrisTest.Stress.Params.vofe.ne` -/
#guard_msgs in #check @vofe.ne

end

-- BUG (usability): binders of a function-typed result are named `a`, `a_1` in `unfold` and
-- `i`, `i_1` in `absorbing` (not `m`, `b` from the body, as the instance hypothesis uses).
icofix fres6 (P : PROP) : Nat → Bool → PROP := fun m b => iprop(P ∗ ▷ fres6 P (m + 1) !b)
/--
info: @fres6.unfold : ∀ {PROP : Type u_1} [inst : BI PROP] (P : PROP) (a : Nat) (a_1 : Bool),
  fres6 P a a_1 = fres6.pre fres6 P a a_1
-/
#guard_msgs in #check @fres6.unfold
/--
info: @fres6.absorbing : ∀ {PROP : Type u_1} [inst : BI PROP]
  [h : ∀ (P : PROP) (m : Nat) (b : Bool), Absorbing (fres6.pre (fun P i i_1 => iprop(<absorb> fres6 P i i_1)) P m b)]
  (P : PROP) (i : Nat) (i_1 : Bool), Absorbing (fres6 P i i_1)
-/
#guard_msgs in #check @fres6.absorbing

-- An implicit varying parameter gives an explicit motive `Φ : Nat → PROP`.
/--
info: @imv.iter : ∀ {PROP : Type u_1} [inst : BI PROP] (Φ : Nat → PROP), ⊢ (□ ∀ n, imv.pre Φ -∗ Φ n) -∗ ∀ n, imv -∗ Φ n
-/
#guard_msgs in #check @imv.iter

-- A parameter `n` keeps its name; `ne` primes its step index `n'`, and the functions `f'`.
section
variable {α : Type _}
ifix neClash [OFE α] (f : α → α) (x y : α) (n : Nat) : PROP := iprop% ▷ neClash f y x (n + 1)
/--
info: @neClash.ne : ∀ {PROP : Type u_1} [inst : BI PROP] {α : Type u_2} [inst_1 : OFE α] {n' : Nat},
  (∀ (f' g : (α → α) → α → α → Nat → PROP),
      (∀ (f f'_1 : α → α),
          f ≡{n'}≡ f'_1 →
            ∀ (x x' : α), x ≡{n'}≡ x' → ∀ (y y' : α), y ≡{n'}≡ y' → ∀ (n : Nat), f' f x y n ≡{n'}≡ g f'_1 x' y' n) →
        ∀ (f f'_1 : α → α),
          f ≡{n'}≡ f'_1 →
            ∀ (x x' : α),
              x ≡{n'}≡ x' →
                ∀ (y y' : α), y ≡{n'}≡ y' → ∀ (n : Nat), neClash.pre f' f x y n ≡{n'}≡ neClash.pre g f'_1 x' y' n) →
    ∀ (f f' : α → α),
      f ≡{n'}≡ f' →
        ∀ (x x' : α), x ≡{n'}≡ x' → ∀ (y y' : α), y ≡{n'}≡ y' → ∀ (n : Nat), neClash f x y n ≡{n'}≡ neClash f' x' y' n
-/
#guard_msgs in #check @neClash.ne
end

end IrisTest.Stress.Params
