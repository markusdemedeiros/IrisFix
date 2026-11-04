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

/-! ## Zero varying parameters -/

ifix f1 (P : PROP) : PROP := iprop% P ∗ ▷ f1 P

example (P : PROP) : f1 P = f1.pre P (f1 P) := f1.unfold P
example (P Φ : PROP) : ⊢ □ (f1.pre P Φ -∗ Φ) -∗ f1 P -∗ Φ := f1.iter P Φ
example [BIAffine PROP] (P : PROP) : Affine (f1 P) := inferInstance

/-! ## Fixed and varying, in every order -/

-- Fixed last.
ifix fl (n : Nat) (P : PROP) : PROP := iprop% P ∨ ▷ fl (n + 1) P

example (n : Nat) (P : PROP) : fl n P = fl.pre P (fun n => fl n P) n := fl.unfold n P
example (P : PROP) (Φ : Nat → PROP) :
    ⊢ □ (∀ n, iprop(P ∨ ▷ Φ (n + 1)) -∗ Φ n) -∗ ∀ n, fl n P -∗ Φ n :=
  fl.iter P Φ
example (P : PROP) (Φ : Nat → PROP) :
    ⊢ □ (∀ n, fl.pre P (fun n => iprop(Φ n ∧ fl n P)) n -∗ Φ n) -∗ ∀ n, fl n P -∗ Φ n :=
  fl.ind P Φ
example (P : PROP) [Persistent P] [Absorbing P] (n : Nat) : Persistent (fl n P) := inferInstance
example [BIAffine PROP] (P : PROP) (n : Nat) : Affine (fl n P) := inferInstance

icofix cfl (n : Nat) (P : PROP) : PROP := iprop% P ∗ ▷ cfl (n + 1) P

example (n : Nat) (P : PROP) : cfl n P = cfl.pre P (fun n => cfl n P) n := cfl.unfold n P
example (P : PROP) (Φ : Nat → PROP) :
    ⊢ □ (∀ n, Φ n -∗ cfl.pre P Φ n) -∗ ∀ n, Φ n -∗ cfl n P := cfl.coiter P Φ

-- Interleaved: F V F V F V.
ifix il (a : Nat) (x : Nat) (b : Bool) (y : Bool) (P : PROP) (z : Nat) : PROP :=
  iprop(P ∨ ▷ il a (x + 1) b (!y) P (z + a))

example (a x : Nat) (b y : Bool) (P : PROP) (z : Nat) :
    il a x b y P z = il.pre a b P (fun x y => il a x b y P) x y z :=
  il.unfold a x b y P z
example (a : Nat) (b : Bool) (P : PROP) (Φ : Nat → Bool → Nat → PROP) :
    ⊢ □ (∀ x y z, il.pre a b P Φ x y z -∗ Φ x y z) -∗ ∀ x y z, il a x b y P z -∗ Φ x y z :=
  il.iter a b P Φ
example (a : Nat) (b : Bool) (P : PROP) (Φ W : Nat → Bool → Nat → PROP)
    (hW : ∀ x y z, iprop(Φ x y z ∧ il.pre a b P W x y z) ⊢ W x y z) :
    ⊢ □ (∀ x y z, il.pre a b P W x y z -∗ Φ x y z) -∗ ∀ x y z, il a x b y P z -∗ Φ x y z :=
  il.ind_wf a b P Φ W hW
example (a : Nat) (b : Bool) (P : PROP) (G : (Nat → Bool → Nat → PROP) → Nat → Bool → Nat → PROP)
    (g : Nat → Bool → Nat → PROP) (hg : ∀ x y z, G g x y z ⊢ g x y z) :
    ⊢ □ (∀ Φ x y z, il.pre a b P Φ x y z -∗ G Φ x y z) -∗ ∀ x y z, il a x b y P z -∗ g x y z :=
  il.strong_mono a b P G g hg

-- Interleaved: V F V F, greatest fixpoint.
icofix il2 (x : Nat) (a : Nat) (y : Bool) (b : Bool) : PROP :=
  iprop(⌜a = x⌝ ∗ ▷ il2 (x + 1) a (!y) b)

example (x a : Nat) (y b : Bool) : il2 (PROP := PROP) x a y b = il2.pre a b (fun x y => il2 x a y b) x y :=
  il2.unfold x a y b
example (a : Nat) (b : Bool) (Φ W : Nat → Bool → PROP) (hW : ∀ x y, W x y ⊢ iprop(Φ x y ∨ il2.pre a b W x y)) :
    ⊢ □ (∀ x y, Φ x y -∗ il2.pre a b W x y) -∗ ∀ x y, Φ x y -∗ il2 x a y b :=
  il2.paco a b Φ W hW
example (a : Nat) (b : Bool) (x : Nat) (y : Bool) : Absorbing (il2 (PROP := PROP) x a y b) := inferInstance

-- Four varying, four fixed, interleaved.
ifix big (a : Nat) (P : PROP) (b : Bool) (Q : PROP) (c : Nat) (R : PROP) (d : Bool) (S : PROP) :
    PROP :=
  iprop(P ∗ Q ∗ R ∗ S ∨ ▷ big (a + 1) P (!b) Q (c + 1) R (!d) S)

example (P Q R S : PROP) (Φ : Nat → Bool → Nat → Bool → PROP) :
    ⊢ □ (∀ a b c d, big.pre P Q R S Φ a b c d -∗ Φ a b c d) -∗
      ∀ a b c d, big a P b Q c R d S -∗ Φ a b c d :=
  big.iter P Q R S Φ

-- A parameter swapped with another varies.
ifix sw2 (a b : Nat) : PROP := iprop% ⌜a = b⌝ ∨ ▷ sw2 b a
example (Φ : Nat → Nat → PROP) :
    ⊢ □ (∀ a b, sw2.pre Φ a b -∗ Φ a b) -∗ ∀ a b, sw2 a b -∗ Φ a b := sw2.iter Φ

-- A bare recursive reference keeps every argument varying.
ifix bare (n : Nat) (P : PROP) : PROP := let next := bare; iprop(P ∨ ▷ next (n + 1) P)
example (Φ : Nat → PROP → PROP) :
    ⊢ □ (∀ n P, bare.pre Φ n P -∗ Φ n P) -∗ ∀ n P, bare n P -∗ Φ n P := bare.iter Φ

/-! ## Implicit, strict-implicit, instance-implicit binders -/

-- Implicit fixed.
ifix imf {P : PROP} (n : Nat) : PROP := iprop% P ∨ imf (P := P) (n + 1)
example (P : PROP) (Φ : Nat → PROP) :
    ⊢ □ (∀ n, imf.pre (P := P) Φ n -∗ Φ n) -∗ ∀ n, imf (P := P) n -∗ Φ n := imf.iter Φ

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

-- Instance-implicit fixed, after a varying parameter.
ifix late (n : Nat) {α : Type} [Inhabited α] : PROP := iprop% ⌜n = 0⌝ ∨ ▷ late (α := α) (n + 1)
example {α : Type} [Inhabited α] (Φ : Nat → PROP) :
    ⊢ □ (∀ n, late.pre (α := α) Φ n -∗ Φ n) -∗ ∀ n, late (α := α) n -∗ Φ n := late.iter Φ
example [BIAffine PROP] {α : Type} [Inhabited α] (n : Nat) : Affine (late (PROP := PROP) n (α := α)) :=
  inferInstance

-- Instance-implicit varying (the instance varies with `b`).
ifix instv (b : Bool) [Decidable (b = true)] : PROP := iprop% ⌜b = true⌝ ∨ instv (!b)
example [BIAffine PROP] (b : Bool) : Persistent (instv (PROP := PROP) b) := inferInstance

/-! ## Dependent parameters -/

-- Varying depends on fixed.
ifix dep1 (n : Nat) (i : Fin (n + 1)) : PROP := iprop% ⌜i.val = 0⌝ ∨ ▷ dep1 n 0
example (n : Nat) (Φ : Fin (n + 1) → PROP) :
    ⊢ □ (∀ i, dep1.pre n Φ i -∗ Φ i) -∗ ∀ i, dep1 n i -∗ Φ i := dep1.iter n Φ

-- Varying depends on varying.
ifix dep2 (n : Nat) (i : Fin (n + 1)) : PROP := iprop% ⌜i.val = 0⌝ ∨ ▷ dep2 (n + 1) 0
example (Φ : (n : Nat) → Fin (n + 1) → PROP) :
    ⊢ □ (∀ n i, dep2.pre (fun n i => iprop(Φ n i ∧ dep2 n i)) n i -∗ Φ n i) -∗
      ∀ n i, dep2 n i -∗ Φ n i := dep2.ind Φ

-- Fixed between two varying ones, the later varying one depending on it.
ifix dep5 (x : Nat) (n : Nat) (v : Fin (n + 1)) : PROP := iprop% ⌜v.val = x⌝ ∨ ▷ dep5 (x + 1) n 0
example (x n : Nat) (v : Fin (n + 1)) :
    dep5 (PROP := PROP) x n v = dep5.pre n (fun x => dep5 x n) x v := dep5.unfold x n v
example (n : Nat) (Φ : Nat → Fin (n + 1) → PROP) :
    ⊢ □ (∀ x v, iprop(⌜v.val = x⌝ ∨ ▷ Φ (x + 1) 0) -∗ Φ x v) -∗ ∀ x v, dep5 x n v -∗ Φ x v :=
  dep5.iter n Φ
example [BIAffine PROP] (x n : Nat) (v : Fin (n + 1)) : Affine (dep5 (PROP := PROP) x n v) :=
  inferInstance

-- Fixed parameters whose types depend on each other, after... and before a varying one.
ifix dep4 (n : Nat) (v : Fin (n + 1)) (k : Nat) : PROP := iprop% ⌜v.val = k⌝ ∨ ▷ dep4 n v (k + 1)
example (n : Nat) (v : Fin (n + 1)) (Φ : Nat → PROP) :
    ⊢ □ (∀ k, dep4.pre n v Φ k -∗ Φ k) -∗ ∀ k, dep4 n v k -∗ Φ k := dep4.iter n v Φ

-- Auto-bound implicit fixed, mentioned only in the type of a varying parameter.
ifix dep3 (_i : Fin (n + 1)) (P : PROP) : PROP := iprop% P ∨ ▷ dep3 (n := n) 0 P
example {n : Nat} (P : PROP) (Φ : Fin (n + 1) → PROP) :
    ⊢ □ (∀ i, dep3.pre P Φ i -∗ Φ i) -∗ ∀ i, dep3 i P -∗ Φ i := dep3.iter P Φ

/-! ## Prop-, Type- and universe-polymorphic parameters -/

ifix propv (p : Prop) : PROP := iprop% ⌜p⌝ ∨ ▷ propv (¬p)
example (Φ : Prop → PROP) : ⊢ □ (∀ p, propv.pre Φ p -∗ Φ p) -∗ ∀ p, propv p -∗ Φ p := propv.iter Φ

-- A proof as a fixed parameter is fine.
ifix prff (n : Nat) (h : n > 0) (k : Nat) : PROP := iprop% ⌜k = n⌝ ∨ ▷ prff n h (k + 1)
example (n : Nat) (h : n > 0) (Φ : Nat → PROP) :
    ⊢ □ (∀ k, prff.pre n h Φ k -∗ Φ k) -∗ ∀ k, prff n h k -∗ Φ k := prff.iter n h Φ

ifix typev (α : Type) : PROP := iprop% ⌜Nonempty α⌝ ∨ ▷ typev (List α)
example (α : Type) : Persistent (typev (PROP := PROP) α) := inferInstance

ifix typef (α : Type) (xs : List α) : PROP :=
  iprop(⌜xs = []⌝ ∨ ∃ x ys, ⌜xs = x :: ys⌝ ∗ typef α ys)
example (α : Type) (Φ : List α → PROP) :
    ⊢ □ (∀ xs, typef.pre α Φ xs -∗ Φ xs) -∗ ∀ xs, typef α xs -∗ Φ xs := typef.iter α Φ

universe u w

ifix upoly {α : Type u} (xs : List α) : PROP :=
  iprop(⌜xs = []⌝ ∨ ∃ x ys, ⌜xs = x :: ys⌝ ∗ upoly ys)
example {α : Type u} (Φ : List α → PROP) :
    ⊢ □ (∀ xs, upoly.pre Φ xs -∗ Φ xs) -∗ ∀ xs, upoly xs -∗ Φ xs := upoly.iter Φ

-- A varying `Sort`.
ifix uvary (α : Sort u) : PROP := iprop% ⌜Nonempty α⌝ ∨ ▷ uvary (α → α)
example (Φ : Sort u → PROP) :
    ⊢ □ (∀ (α : Sort u), uvary.pre Φ α -∗ Φ α) -∗ ∀ (α : Sort u), uvary α -∗ Φ α := uvary.iter Φ

-- Own BI, with a fixed `Sort w` domain.
ifix uu {PROP' : Type u} [BI PROP'] {α : Sort w} (f : α → Nat) (x : α) (n : Nat) : PROP' :=
  iprop(⌜f x = n⌝ ∨ ▷ uu f x (n + 1))
/--
info: @uu.iter : ∀ {PROP' : Type u_1} [inst : BI PROP'] {α : Sort u_2} (f : α → Nat) (x : α) (Φ : Nat → PROP'),
  ⊢ (□ ∀ n, uu.pre f x Φ n -∗ Φ n) -∗ ∀ n, uu f x n -∗ Φ n
-/
#guard_msgs in #check @uu.iter

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
example (n : Nat) (Φ : (Nat → Nat) → PROP) :
    ⊢ □ (∀ f, funv.pre n Φ f -∗ Φ f) -∗ ∀ f, funv f n -∗ Φ f := funv.iter n Φ

ifix funf (f : Nat → Nat) (n : Nat) : PROP := iprop% ⌜f n = 0⌝ ∨ ▷ funf f (f n)
example (f : Nat → Nat) (Φ : Nat → PROP) :
    ⊢ □ (∀ n, funf.pre f Φ n -∗ Φ n) -∗ ∀ n, funf f n -∗ Φ n := funf.iter f Φ

ifix hof (Q : Nat → PROP) (n : Nat) : PROP := iprop% Q n ∨ ▷ hof Q (n + 1)
example (Q Φ : Nat → PROP) :
    ⊢ □ (∀ n, iprop(Q n ∨ ▷ Φ (n + 1)) -∗ Φ n) -∗ ∀ n, hof Q n -∗ Φ n := hof.iter Q Φ

/-! ## Section variables, defaults, no type, `fun` with alternatives -/

section
variable (Q : PROP)
ifix sv (n : Nat) : PROP := iprop% Q ∨ ▷ sv (n + 1)
example (Φ : Nat → PROP) : ⊢ □ (∀ n, sv.pre Q Φ n -∗ Φ n) -∗ ∀ n, sv Q n -∗ Φ n := sv.iter Q Φ
end

ifix noty (n : Nat) := iprop% ⌜n = 0⌝ ∨ ▷ (noty (n + 1) : PROP)
example (Φ : Nat → PROP) : ⊢ □ (∀ n, noty.pre Φ n -∗ Φ n) -∗ ∀ n, noty n -∗ Φ n := noty.iter Φ

ifix pm (P : PROP) : Nat → PROP := fun
  | 0 => P
  | n + 1 => iprop(▷ pm P n)
example (P : PROP) (Φ : Nat → PROP) :
    ⊢ □ (∀ n, pm.pre P Φ n -∗ Φ n) -∗ ∀ n, pm P n -∗ Φ n := pm.iter P Φ

/-! ## Result types that are not literally `PROP` -/

abbrev MyProp (PROP : Type _) := PROP
ifix abr (n : Nat) : MyProp PROP := iprop% ⌜n = 0⌝ ∨ ▷ abr (n + 1)
example (Φ : Nat → PROP) : ⊢ □ (∀ n, abr.pre Φ n -∗ Φ n) -∗ ∀ n, abr n -∗ Φ n := abr.iter Φ

@[reducible] def RP (PROP : Type _) := PROP
ifix rdw (n : Nat) : Nat → RP PROP := fun m => iprop(⌜n = m⌝ ∨ ▷ rdw (n + 1) (m + 1))
example [BIAffine PROP] (n m : Nat) : Affine (rdw (PROP := PROP) n m) := inferInstance

-- Function-typed result: its parameters are inferred too (`m` fixed here).
ifix fres (n : Nat) : Nat → PROP := fun m => iprop(⌜n = m⌝ ∨ ▷ fres (n + 1) m)
example (n m : Nat) : fres (PROP := PROP) n m = fres.pre m (fun n => fres n m) n := fres.unfold n m
example (m : Nat) (Φ : Nat → PROP) :
    ⊢ □ (∀ n, fres.pre m Φ n -∗ Φ n) -∗ ∀ n, fres n m -∗ Φ n := fres.iter m Φ

icofix fres5 (P : PROP) : Nat → Bool → PROP := fun m b => iprop(P ∗ ▷ fres5 P (m + 1) !b)
example (P : PROP) [Absorbing P] (m : Nat) (b : Bool) : Absorbing (fres5 P m b) := inferInstance
example (P : PROP) (Φ : Nat → Bool → PROP) :
    ⊢ □ (∀ m b, Φ m b -∗ iprop(P ∗ ▷ Φ (m + 1) !b)) -∗ ∀ m b, Φ m b -∗ fres5 P m b :=
  fres5.coiter P Φ

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

-- Both varying, with OFEs: `ne`.
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

-- An OFE parameter that is fixed: no `ne` (the spec asks for `ne` only for varying ones).
ifix ofix [OFE α] (x : α) (k : Nat) : PROP := iprop% ▷ ofix x (k + 1)
/--
error: Unknown constant `IrisTest.Stress.Params.ofix.ne`
-/
#guard_msgs in #check @ofix.ne
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
example (k : Nat) (Φ : Nat → PROP) :
    ⊢ □ (∀ n, dv.pre k Φ n -∗ Φ n) -∗ ∀ n, dv n k -∗ Φ n := dv.iter k Φ

/-! ## Limitations and remaining bugs -/

section
variable {α : Type _}

-- Limitation: varying parameters of type `Prop`/`Sort` (here a proof) are out of scope.
/--
error: ifix_monotone: the order of
  (n : Nat) → n > 0 → PROP
is not the order of `IOrder`
-/
#guard_msgs in
ifix prfv (n : Nat) (h : n > 0) : PROP := iprop% ⌜n = 1⌝ ∨ ▷ prfv (n + 1) (Nat.succ_pos n)

-- Limitation: same, for an implicit proof parameter.
/--
error: ifix_monotone: the order of
  (n : Nat) → {h : n > 0} → PROP
is not the order of `IOrder`
-/
#guard_msgs in
ifix prfi (n : Nat) {h : n > 0} : PROP := iprop% ⌜n = 1⌝ ∨ ▷ prfi (n + 1) (h := Nat.succ_pos n)

-- Limitation: same, for an autoParam (a proof) that varies.
/--
error: ifix_monotone: the order of
  (n : Nat) → autoParam (n = n) ap._auto_1 → PROP
is not the order of `IOrder`
-/
#guard_msgs in
ifix ap (n : Nat) (h : n = n := by rfl) : PROP := iprop% ⌜n = 0⌝ ∨ ▷ ap (n + 1)

-- Limitation: same, for a varying parameter whose type lives in `Sort w`.
/--
error: ifix_monotone: the order of
  β → PROP
is not the order of `IOrder`
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
  fres6 P a a_1 = fres6.pre P (fres6 P) a a_1
-/
#guard_msgs in #check @fres6.unfold
/--
info: @fres6.absorbing : ∀ {PROP : Type u_1} [inst : BI PROP] (P : PROP)
  [h : ∀ (m : Nat) (b : Bool), Absorbing (fres6.pre P (fun i i_1 => iprop(<absorb> fres6 P i i_1)) m b)] (i : Nat)
  (i_1 : Bool), Absorbing (fres6 P i i_1)
-/
#guard_msgs in #check @fres6.absorbing

-- An implicit varying parameter gives an explicit motive `Φ : Nat → PROP`.
/--
info: @imv.iter : ∀ {PROP : Type u_1} [inst : BI PROP] (Φ : Nat → PROP), ⊢ (□ ∀ n, imv.pre Φ -∗ Φ n) -∗ ∀ n, imv -∗ Φ n
-/
#guard_msgs in #check @imv.iter

-- BUG (usability): `ne` names its step index `n`; a parameter `n` becomes `n_1` instead of the
-- step index being primed. (The functions `f g` are now primed: `f'`.)
section
variable {α : Type _}
ifix neClash [OFE α] (f : α → α) (x y : α) (n : Nat) : PROP := iprop% ▷ neClash f y x (n + 1)
/--
info: @neClash.ne : ∀ {PROP : Type u_1} [inst : BI PROP] {α : Type u_2} [inst_1 : OFE α] (f : α → α) {n : Nat},
  (∀ (f' g : α → α → Nat → PROP),
      (∀ (x x' : α), x ≡{n}≡ x' → ∀ (y y' : α), y ≡{n}≡ y' → ∀ (n_1 : Nat), f' x y n_1 ≡{n}≡ g x' y' n_1) →
        ∀ (x x' : α),
          x ≡{n}≡ x' →
            ∀ (y y' : α), y ≡{n}≡ y' → ∀ (n_1 : Nat), neClash.pre f f' x y n_1 ≡{n}≡ neClash.pre f g x' y' n_1) →
    ∀ (x x' : α), x ≡{n}≡ x' → ∀ (y y' : α), y ≡{n}≡ y' → ∀ (n_1 : Nat), neClash f x y n_1 ≡{n}≡ neClash f x' y' n_1
-/
#guard_msgs in #check @neClash.ne
end

end IrisTest.Stress.Params
