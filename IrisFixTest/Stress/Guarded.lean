/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.BI
public import IrisFix.ProofMode.Lib.Fixpoint
public import IrisFix.ProofMode.Lib.Guarded
public import IrisFix.BI.Lib.FixpointBanach

/-! # Stress tests for `iguarded` -/

@[expose] public section
open Iris BI OFE

namespace IrisTest.Stress.Guarded

local bi PROP

variable {PROP : Type _} [BI PROP] [BILaterContractive PROP] [Inhabited PROP]

/-! ## Binder shapes that work -/

-- Zero binders.
iguarded z0 : PROP := iprop% ▷ z0
contractive_by
  intros k Φ Ψ h; unfold z0.pre; exact Contractive.distLater_dist h

example : z0 (PROP := PROP) = z0.pre z0 := z0.unfold

-- Match alternatives.
iguarded galt : Nat → PROP
  | 0 => iprop% True
  | n + 1 => iprop% ▷ galt n
contractive_by
  intros k Φ Ψ h n
  cases n
  · rfl
  · dsimp only [galt.pre]; exact Contractive.distLater_dist (fun m hm => h m hm _)

example (n : Nat) : galt (PROP := PROP) (n + 1) = iprop(▷ galt n) := galt.unfold (n + 1)
example : z0 (PROP := PROP) = iprop(▷ z0) := z0.unfold
example : z0 (PROP := PROP) = fixpoint z0.pre := z0.eq_fixpoint
example : (∀ Φ : PROP, Persistent Φ → Persistent (z0.pre Φ)) → Persistent (z0 (PROP := PROP)) :=
  z0.persistent
example : (∀ Φ : PROP, Absorbing Φ → Absorbing (z0.pre Φ)) → Absorbing (z0 (PROP := PROP)) :=
  z0.absorbing
example : (∀ Φ : PROP, Affine Φ → Affine (z0.pre Φ)) → Affine (z0 (PROP := PROP)) :=
  z0.affine
example : (∀ Φ : PROP, Persistent Φ → Absorbing Φ → Persistent (z0.pre Φ) ∧ Absorbing (z0.pre Φ)) →
    Persistent (z0 (PROP := PROP)) ∧ Absorbing (z0 (PROP := PROP)) :=
  z0.persistent_absorbing
example : (∀ Φ : PROP, Persistent Φ → Affine Φ → Persistent (z0.pre Φ) ∧ Affine (z0.pre Φ)) →
    Persistent (z0 (PROP := PROP)) ∧ Affine (z0 (PROP := PROP)) :=
  z0.persistent_affine
example : Persistent (z0 (PROP := PROP)) :=
  z0.persistent fun _ _ => by unfold z0.pre; infer_instance
example : Absorbing (z0 (PROP := PROP)) :=
  z0.absorbing fun _ _ => by unfold z0.pre; infer_instance

-- Three binders, two recursive occurrences.
iguarded t3 (a : Nat) (b : Bool) (c : Int) : PROP := iprop% ▷ t3 a b c ∗ ▷ t3 (a+1) (!b) (c-1)
contractive_by
  intros k Φ Ψ h a b c; unfold t3.pre
  exact sep_ne.ne (Contractive.distLater_dist fun m hm => h m hm _ _ _)
    (Contractive.distLater_dist fun m hm => h m hm _ _ _)

example (a : Nat) (b : Bool) (c : Int) :
    t3 (PROP := PROP) a b c = iprop(▷ t3 a b c ∗ ▷ t3 (a+1) (!b) (c-1)) := t3.unfold a b c
example : (∀ Φ : Nat → Bool → Int → PROP,
      (∀ a b c, Persistent (Φ a b c)) → (∀ a b c, Absorbing (Φ a b c)) →
        ∀ a b c, Persistent (t3.pre Φ a b c) ∧ Absorbing (t3.pre Φ a b c)) →
    ∀ a b c, Persistent (t3 (PROP := PROP) a b c) ∧ Absorbing (t3 (PROP := PROP) a b c) :=
  t3.persistent_absorbing
example (a : Nat) (b : Bool) (c : Int) : Absorbing (t3 (PROP := PROP) a b c) :=
  t3.absorbing (fun _ _ _ _ _ => by unfold t3.pre; infer_instance) a b c

-- Grouped binders.
iguarded grp (a b : Nat) : PROP := iprop% ▷ grp b a
contractive_by
  intros k Φ Ψ h a b; unfold grp.pre; exact Contractive.distLater_dist (fun m hm => h m hm _ _)

example (a b : Nat) : grp (PROP := PROP) a b = iprop(▷ grp b a) := grp.unfold a b

-- Strict implicit binder.
iguarded sim ⦃n : Nat⦄ : PROP := iprop% ▷ sim (n := n+1)
contractive_by
  intros k Φ Ψ h n; unfold sim.pre; exact Contractive.distLater_dist (fun m hm => h m hm _)

example (n : Nat) : sim (PROP := PROP) (n := n) = iprop(▷ sim (n := n+1)) := sim.unfold (n := n)

-- Implicit binder after an explicit one.
iguarded mi (n : Nat) {m : Nat} : PROP := iprop% ▷ mi (n+1) (m := m+1)
contractive_by
  intros k Φ Ψ h n m; unfold mi.pre
  exact Contractive.distLater_dist (fun j hj => (h j hj (n+1)) (m+1))

example (n m : Nat) : mi (PROP := PROP) n (m := m) = iprop(▷ mi (n+1) (m := m+1)) := mi.unfold n

-- Type parameter, polymorphic recursion, universe parameter, large universe.
iguarded poly (α : Type) (x : α) : PROP := iprop% ▷ poly (List α) [x]
contractive_by
  intros k Φ Ψ h α x; unfold poly.pre; exact Contractive.distLater_dist (fun m hm => h m hm _ _)

example (α : Type) (x : α) : poly (PROP := PROP) α x = iprop(▷ poly (List α) [x]) :=
  poly.unfold α x

universe u
iguarded up (α : Type u) (x : α) : PROP := iprop% ▷ up α x
contractive_by
  intros k Φ Ψ h α x; unfold up.pre; exact Contractive.distLater_dist (fun m hm => h m hm _ _)

example (α : Type 2) (x : α) : up (PROP := PROP) α x = iprop(▷ up α x) := up.unfold α x

-- Dependent binders.
iguarded dep (n : Nat) (v : Fin (n+1)) : PROP := iprop% ▷ dep (n+1) v.succ
contractive_by
  intros k Φ Ψ h n v; unfold dep.pre; exact Contractive.distLater_dist (fun m hm => h m hm _ _)

example (n : Nat) (v : Fin (n + 1)) : dep (PROP := PROP) n v = iprop(▷ dep (n + 1) v.succ) :=
  dep.unfold n v
example : (∀ Φ : (n : Nat) → Fin (n+1) → PROP, (∀ n v, Persistent (Φ n v)) →
      ∀ n v, Persistent (dep.pre Φ n v)) → ∀ n v, Persistent (dep (PROP := PROP) n v) :=
  dep.persistent

-- Instance-implicit binder after an explicit one.
iguarded ii (α : Type) [Inhabited α] (n : Nat) : PROP := iprop% ▷ ii α (n+1)
contractive_by
  intros k Φ Ψ h α _ n; unfold ii.pre; exact Contractive.distLater_dist (fun m hm => h m hm _ _ _)

example (n : Nat) : ii (PROP := PROP) Nat n = iprop(▷ ii Nat (n+1)) := ii.unfold Nat n

-- Limitation: a varying auto-bound `β : Sort ?u` (the `Sort` limitation), reported by `mkAppOptM` with a
-- universe metavariable.
/--
error: AppBuilder for `mkAppOptM`, result contains metavariables
  bind₂ approx fun self x => iprop(▷ self x)
---
warning: unused `partial_fixpoint`, function is not recursive
-/
#guard_msgs in
iguarded ab (x : β) : PROP := iprop% ▷ ab x
contractive_by
  intros k Φ Ψ h x; unfold ab.pre; exact Contractive.distLater_dist (fun m hm => h m hm _)

-- Implicit section variable used in the binder types.
section
variable {γ : Type}
iguarded sv1 (x : γ) : PROP := iprop% ▷ sv1 x
contractive_by
  intros k Φ Ψ h x; unfold sv1.pre; exact Contractive.distLater_dist (fun m hm => h m hm _)

example (x : γ) : sv1 (PROP := PROP) x = iprop(▷ sv1 x) := sv1.unfold x
end

-- A shadowing binder: the parameter has the name of the definition.
iguarded sh (sh : Nat) : PROP := iprop% ▷ ⌜sh = 0⌝
contractive_by
  intros _ _ _ _ _; rfl

example (n : Nat) : sh (PROP := PROP) n = iprop(▷ ⌜n = 0⌝) := sh.unfold n

-- A leading instance-implicit binder: a fixed parameter.
iguarded k0 [Inhabited Nat] : PROP := iprop% ▷ k0
contractive_by
  intros k Φ Ψ h; unfold k0.pre; exact Contractive.distLater_dist (fun m hm => h m hm)

example : k0 (PROP := PROP) = iprop(▷ k0) := k0.unfold

-- A leading implicit binder.
iguarded imp {n : Nat} : PROP := iprop% ▷ imp (n := n+1)
contractive_by
  intros k Φ Ψ h n; unfold imp.pre; exact Contractive.distLater_dist (fun m hm => h m hm (n+1))

example (n : Nat) : imp (PROP := PROP) (n := n) = iprop(▷ imp (n := n+1)) := imp.unfold

-- Implicit section variable used only in the body.
section
variable {Q : PROP}
iguarded svi (n : Nat) : PROP := iprop% Q ∗ ▷ svi (n+1)
contractive_by
  intros k Φ Ψ h n; unfold svi.pre
  exact sep_ne.ne .rfl (Contractive.distLater_dist (fun m hm => h m hm _))

example (n : Nat) : svi (Q := Q) n = iprop(Q ∗ ▷ svi (Q := Q) (n+1)) := svi.unfold n
end

-- Explicit section variable used only in the body.
section
variable (P : PROP)
iguarded sv (n : Nat) : PROP := iprop% P ∗ ▷ sv (n+1)
contractive_by
  intros k Φ Ψ h n; unfold sv.pre
  exact sep_ne.ne .rfl (Contractive.distLater_dist (fun m hm => h m hm _))

example (n : Nat) : sv P n = iprop(P ∗ ▷ sv P (n+1)) := sv.unfold P n
end

-- `_root_` and dotted names.
iguarded _root_.rootg (n : Nat) : PROP := iprop% ▷ rootg (n+1)
contractive_by
  intros k Φ Ψ h n; unfold rootg.pre; exact Contractive.distLater_dist (fun m hm => h m hm _)

example (n : Nat) : _root_.rootg (PROP := PROP) n = iprop(▷ rootg (n+1)) := _root_.rootg.unfold n

iguarded Foo.bar (n : Nat) : PROP := iprop% ▷ Foo.bar (n+1)
contractive_by
  intros k Φ Ψ h n; unfold Foo.bar.pre; exact Contractive.distLater_dist (fun m hm => h m hm _)

example (n : Nat) : Foo.bar (PROP := PROP) n = iprop(▷ Foo.bar (n+1)) := Foo.bar.unfold n

-- A non-recursive body.
iguarded nr (n : Nat) : PROP := iprop% ⌜n = 0⌝
contractive_by
  intros _ _ _ _ _; rfl

example (n : Nat) : nr (PROP := PROP) n = iprop(⌜n = 0⌝) := nr.unfold n

/-! ## Result types and bodies that work -/

-- A function type, no binders.
iguarded fr : Nat → PROP := fun n => iprop(▷ fr (n+1))
contractive_by
  intros k Φ Ψ h n; unfold fr.pre; exact Contractive.distLater_dist (fun m hm => h m hm _)

example (n : Nat) : fr (PROP := PROP) n = iprop(▷ fr (n+1)) := fr.unfold n

-- A function type after binders.
iguarded gm (n : Nat) : Bool → Nat → PROP := fun b m => iprop(▷ gm (n+m) (!b) m)
contractive_by
  intros k Φ Ψ h n b m; unfold gm.pre; exact Contractive.distLater_dist (fun m hm => h m hm _ _ _)

example (n : Nat) (b : Bool) (m : Nat) : gm (PROP := PROP) n b m = iprop(▷ gm (n+m) (!b) m) :=
  gm.unfold n b m

-- Negative occurrence.
iguarded neg (n : Nat) : PROP := iprop% ▷ neg n -∗ False
contractive_by
  intros k Φ Ψ h n; unfold neg.pre
  exact wand_ne.ne (Contractive.distLater_dist (fun m hm => h m hm _)) .rfl

example (n : Nat) : neg (PROP := PROP) n = iprop(▷ neg n -∗ False) := neg.unfold n

-- `▷` under a quantifier.
iguarded fa (n : Nat) : PROP := iprop% ∀ m, ▷ fa (n + m)
contractive_by
  intros k Φ Ψ h n; unfold fa.pre
  exact forall_ne fun m => Contractive.distLater_dist (fun j hj => h j hj _)

example (n : Nat) : fa (PROP := PROP) n ⊢ ▷ fa (n + 0) := by
  rw [fa.unfold]; iintro H; iapply H

-- A bare reference to the recursive function.
iguarded bare (n : Nat) : PROP := let next := bare; iprop(▷ next (n+1))
contractive_by
  intros k Φ Ψ h n; exact Contractive.distLater_dist (f := BIBase.later) (fun m hm => h m hm _)

example (n : Nat) : bare (PROP := PROP) n = iprop(▷ bare (n+1)) := bare.unfold n

-- The recursive function passed to another function.
def app0 (f : Nat → PROP) : PROP := f 0
iguarded ho (n : Nat) : PROP := iprop% ⌜n = n⌝ ∧ ▷ app0 ho
contractive_by
  intros k Φ Ψ h n; unfold ho.pre
  exact and_ne.ne .rfl (Contractive.distLater_dist (fun m hm => h m hm _))

example (n : Nat) : ho (PROP := PROP) n = iprop(⌜n = n⌝ ∧ ▷ app0 ho) := ho.unfold n

/-! ## `wp`-shaped definitions and using the laws -/

iguarded wp (n : Nat) (Φ : Nat → PROP) : PROP := iprop% □ (Φ n ∨ ▷ wp (n + 1) fun m => Φ (m + 1))
contractive_by
  intros k Ψ₁ Ψ₂ h n Φ; unfold wp.pre
  exact intuitionistically_ne.ne (or_ne.ne .rfl (Contractive.distLater_dist fun m hm => h m hm _ _))

example (n : Nat) (Φ : Nat → PROP) :
    wp n Φ = iprop(□ (Φ n ∨ ▷ wp (n + 1) fun m => Φ (m + 1))) := wp.unfold n Φ

instance (n : Nat) (Φ : Nat → PROP) : Persistent (wp n Φ) :=
  wp.persistent (fun _ _ _ _ => by unfold wp.pre; infer_instance) n Φ

instance (n : Nat) (Φ : Nat → PROP) : Affine (wp n Φ) :=
  wp.affine (fun _ _ _ _ => by unfold wp.pre; infer_instance) n Φ

example (n : Nat) (Φ : Nat → PROP) : Persistent (wp n Φ) ∧ Affine (wp n Φ) :=
  wp.persistent_affine (fun _ _ _ _ _ => by unfold wp.pre; exact ⟨inferInstance, inferInstance⟩) n Φ

-- The derived instances are usable in the proof mode.
example (n : Nat) (Φ : Nat → PROP) : wp n Φ ⊢ □ wp n Φ := by
  iintro #H
  iexact H

example (n : Nat) (Φ : Nat → PROP) : <affine> □ Φ n ⊢ wp n Φ := by
  rw [wp.unfold]
  iintro #H
  imodintro
  ileft
  iexact H

-- A law that needs its hypothesis: `▷` of the recursive call.
iguarded pl (n : Nat) : PROP := iprop% <pers> ▷ pl (n + 1) ∧ ▷ pl (n + 2)
contractive_by
  intros k Φ Ψ h n; unfold pl.pre
  exact and_ne.ne (persistently_ne.ne (Contractive.distLater_dist fun m hm => h m hm _))
    (Contractive.distLater_dist fun m hm => h m hm _)

example (n : Nat) : Persistent (pl (PROP := PROP) n) :=
  pl.persistent (fun _ hΦ n => by unfold pl.pre; have := hΦ (n + 2); infer_instance) n

/-! ## Names that are also global names -/

iguarded later (n : Nat) : PROP := iprop% ▷ later (n+1)
contractive_by
  intros k Φ Ψ h n; unfold later.pre
  exact Contractive.distLater_dist (f := BIBase.later) (fun m hm => h m hm _)

example (n : Nat) : later (PROP := PROP) n = iprop(▷ later (n+1)) := later.unfold n

iguarded fixpoint (n : Nat) : PROP := iprop% ▷ fixpoint (n+1)
contractive_by
  intros k Φ Ψ h n; unfold fixpoint.pre; exact Contractive.distLater_dist (fun m hm => h m hm _)

example : fixpoint (PROP := PROP) = Iris.fixpoint fixpoint.pre := fixpoint.eq_fixpoint

/-! ## Section without `Inhabited PROP` -/

section
variable {PROP' : Type _} [BI PROP'] [BILaterContractive PROP']
iguarded noinh (n : Nat) : PROP' := iprop% ▷ noinh (n+1)
contractive_by
  intros k Φ Ψ h n; unfold noinh.pre; exact Contractive.distLater_dist (fun m hm => h m hm _)

example (n : Nat) : noinh (PROP' := PROP') n = iprop(▷ noinh (n+1)) := noinh.unfold n
end

/-! ## Contractiveness proofs -/

-- Two definitions with the same signature get distinct instances.
iguarded a1 (n : Nat) : PROP := iprop% ▷ a1 (n+1)
contractive_by
  intros k Φ Ψ h n; unfold a1.pre; exact Contractive.distLater_dist (fun m hm => h m hm _)
iguarded a2 (n : Nat) : PROP := iprop% ▷ a2 (n+2)
contractive_by
  intros k Φ Ψ h n; unfold a2.pre; exact Contractive.distLater_dist (fun m hm => h m hm _)
example : Contractive (a1.pre (PROP := PROP)) := inferInstance
example : Contractive (a2.pre (PROP := PROP)) := inferInstance

/-! ## Result types that are not plain BI values -/

-- A COFE result type that is not a BI: no Banach laws.
iguarded pp : PROP × PROP := (iprop(▷ pp.2), iprop(▷ pp.1))
contractive_by
  intros k Φ Ψ h; unfold pp.pre
  exact ⟨Contractive.distLater_dist (f := BIBase.later) (fun m hm => (h m hm).2),
    Contractive.distLater_dist (f := BIBase.later) (fun m hm => (h m hm).1)⟩

example : pp (PROP := PROP) = (iprop(▷ pp.2), iprop(▷ pp.1)) := pp.unfold
example : pp (PROP := PROP) = Iris.fixpoint pp.pre := pp.eq_fixpoint

-- A function type behind a definition is unfolded.
abbrev NP (PROP : Type _) := Nat → PROP
iguarded ga (n : Nat) : NP PROP := fun m => iprop(▷ ga (n+m) m)
contractive_by
  intros k Φ Ψ h n m; unfold ga.pre; exact Contractive.distLater_dist (fun m hm => h m hm _ _)

example (n m : Nat) : ga (PROP := PROP) n m = iprop(▷ ga (n+m) m) := ga.unfold n m
example (n m : Nat) : Persistent (ga (PROP := PROP) n m) :=
  ga.persistent (fun _ _ _ _ => by unfold ga.pre; infer_instance) n m

-- A result type that depends on a parameter only through an `abbrev`.
abbrev Fam (PROP : Type _) (_ : Bool) := PROP
iguarded dd (b : Bool) : Fam PROP b := iprop% ▷ dd (!b)
contractive_by
  intros k Φ Ψ h b; unfold dd.pre; exact Contractive.distLater_dist (fun m hm => h m hm _)

example (b : Bool) : dd (PROP := PROP) b = iprop(▷ dd (!b)) := dd.unfold b

/-! ## Rejected input -/

-- Limitation: a BI-generic definition: the result type depends on the varying `P`.
/--
error: the result type
  Approx P
depends on the parameters
---
warning: unused `partial_fixpoint`, function is not recursive
-/
#guard_msgs in
iguarded gen (P : Type) [BI P] [BILaterContractive P] (n : Nat) : P := iprop% ▷ gen P (n+1)
contractive_by
  intros k Φ Ψ h P _ _ n; unfold gen.pre; exact Contractive.distLater_dist (fun m hm => h m hm _ _ _ _)

-- A type that is not a COFE.
/--
error: failed to synthesize instance of type class
  OFE Nat

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
---
warning: unused `partial_fixpoint`, function is not recursive
-/
#guard_msgs in
iguarded notcofe (n : Nat) : Nat := notcofe n
contractive_by
  intros; rfl

-- Limitation: a proof parameter varies, and `OFE` on `∀ x : α, β x` needs `α : Type` (Sort 0).
/--
error: failed to synthesize
  PointwiseLifting (Approx PROP) ((n : Nat) → 0 < n → Approx PROP)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
---
warning: unused `partial_fixpoint`, function is not recursive
-/
#guard_msgs in
iguarded pr (n : Nat) (h : 0 < n) : PROP := iprop% ▷ pr (n+1) (Nat.lt_succ_of_lt h)
contractive_by
  intros k Φ Ψ h n hn; unfold pr.pre; exact Contractive.distLater_dist (fun m hm => h m hm _ _)

-- Default values are accepted (the laws drop them), as for `ifix`.
iguarded dflt (n : Nat := 0) : PROP := iprop% ▷ dflt (n+1)
contractive_by
  intros k Φ Ψ h n; unfold dflt.pre; exact Contractive.distLater_dist (fun m hm => h m hm _)

example (n : Nat) : dflt (PROP := PROP) n = iprop(▷ dflt (n+1)) := dflt.unfold n

-- A generated name that already exists is rejected.
def clash.pre : Nat := 1
/--
error: cannot generate `IrisTest.Stress.Guarded.clash.pre`: a declaration with this name already exists
-/
#guard_msgs in
iguarded clash (n : Nat) : PROP := iprop% ▷ clash (n+1)
contractive_by
  intros k Φ Ψ h n; unfold clash.pre; exact Contractive.distLater_dist (fun m hm => h m hm _)

-- A missing `contractive_by` fails with a message.
/--
error: iguarded: prove that the body is contractive with `contractive_by`
PROP : Type u_1
inst✝² : BI PROP
inst✝¹ : BILaterContractive PROP
inst✝ : Inhabited PROP
⊢ ∀ {n : Nat} {x y : Nat → PROP}, DistLater n x y → nocon.pre x ≡{n}≡ nocon.pre y
-/
#guard_msgs in
iguarded nocon (n : Nat) : PROP := iprop% ▷ nocon (n+1)

/-! ## Generated declarations -/

-- The contractiveness instance.
example : Contractive (wp.pre (PROP := PROP)) := wp.pre.contractive

-- `eq_fixpoint` holds for any `Inhabited` instance.
example (i : Inhabited (Nat → PROP)) : a1 (PROP := PROP) = @Iris.fixpoint _ _ i a1.pre _ :=
  a1.eq_fixpoint

-- The definition is irreducible.
open Lean Meta in
run_meta guard ((← getReducibilityStatus ``a1) == .irreducible)

-- The Banach law's binder is primed (`Φ'`) so it does not capture the user's `Φ`.
/--
info: @wp.persistent : ∀ {PROP : Type u_1} [inst : BI PROP] [inst_1 : Inhabited PROP] [BILaterContractive PROP],
  (∀ (Φ' : Nat → (Nat → PROP) → PROP),
      (∀ (n : Nat) (Φ : Nat → PROP), Persistent (Φ' n Φ)) → ∀ (n : Nat) (Φ : Nat → PROP), Persistent (wp.pre Φ' n Φ)) →
    ∀ (n : Nat) (Φ : Nat → PROP), Persistent (wp n Φ)
-/
#guard_msgs in
#check @wp.persistent

-- BUG: parameters of a function-typed result are named `a`, `a_1`, not after the body's `fun b m`.
/--
info: @gm.unfold : ∀ {PROP : Type u_1} [inst : BI PROP] [inst_1 : Inhabited PROP] [BILaterContractive PROP] (n : Nat)
  (a : Bool) (a_1 : Nat), gm n a a_1 = gm.pre gm n a a_1
-/
#guard_msgs in
#check @gm.unfold

-- Several BIs in scope: the laws take the right one.
section
variable {S : Type _} [Sbi S] [BILaterContractive S]
set_option iris.localBi.warnOnOverride false in
local bi S
iguarded spl (n : Nat) : S := iprop% ▷ spl (n+1)
contractive_by
  intros k Φ Ψ h n; unfold spl.pre; exact Contractive.distLater_dist (fun m hm => h m hm _)
example (n : Nat) : spl (S := S) n = iprop(▷ spl (n+1)) := spl.unfold n
end

-- Two section variables of the same type, the body uses only `Q`: the definition and laws elaborate.
section
variable (P Q : PROP)
iguarded spq (n : Nat) : PROP := iprop% Q ∗ ▷ spq (n+1)
contractive_by
  intros k Φ Ψ h n; unfold spq.pre
  exact sep_ne.ne .rfl (Contractive.distLater_dist (fun m hm => h m hm _))
#guard_msgs (drop info) in
#check @spq.unfold
end

/-! ## Modifiers and attributes -/

-- `protected`: the short name does not resolve outside the namespace.
protected iguarded pt (n : Nat) : PROP := iprop% ▷ pt (n+1)
contractive_by
  intros k Φ Ψ h n; unfold pt.pre; exact Contractive.distLater_dist (fun m hm => h m hm _)
example : Guarded.pt (PROP := PROP) 0 = iprop(▷ Guarded.pt 1) := Guarded.pt.unfold 0

-- `private`.
private iguarded pv (n : Nat) : PROP := iprop% ▷ pv (n+1)
contractive_by
  intros k Φ Ψ h n; unfold pv.pre; exact Contractive.distLater_dist (fun m hm => h m hm _)
example : pv (PROP := PROP) 0 = iprop(▷ pv 1) := pv.unfold 0

-- BUG: `@[simp]` goes to the definition, so `simp` unfolds `sp` to its internal
-- `(sp.approx ..).get` form, which is useless; expected: `simp` rewrites with `sp.unfold` or leaves
-- `sp` alone.
@[simp] iguarded sp (n : Nat) : PROP := iprop% ▷ sp (n+1)
contractive_by
  intros k Φ Ψ h n; unfold sp.pre; exact Contractive.distLater_dist (fun m hm => h m hm _)
/--
error: unsolved goals
PROP : Type u_1
inst✝² : BI PROP
inst✝¹ : BILaterContractive PROP
inst✝ : Inhabited PROP
⊢ (sp.approx 0).get = iprop(▷ (sp.approx 1).get)
-/
#guard_msgs in
example : sp (PROP := PROP) 0 = iprop(▷ sp 1) := by simp

end IrisTest.Stress.Guarded

/-! ## `plain` laws, in an `Sbi` (outside the namespace, away from the `PROP` variable) -/

namespace IrisTest.Stress.GuardedSbi
local bi S
variable {S : Type _} [Sbi S] [BILaterContractive S]

iguarded spl (n : Nat) : S := iprop% ▷ spl (n+1)
contractive_by
  intros k Φ Ψ h n; unfold spl.pre; exact Contractive.distLater_dist (fun m hm => h m hm _)

example : (∀ Φ : Nat → S, (∀ n, Plain (Φ n)) → ∀ n, Plain (spl.pre Φ n)) →
    ∀ n, Plain (spl (S := S) n) := spl.plain
example (n : Nat) : Plain (spl (S := S) n) ∧ Absorbing (spl (S := S) n) :=
  spl.plain_absorbing (fun _ _ _ n => by unfold spl.pre; exact ⟨inferInstance, inferInstance⟩) n
example : (∀ Φ : Nat → S, (∀ n, Plain (Φ n)) → (∀ n, Affine (Φ n)) →
      ∀ n, Plain (spl.pre Φ n) ∧ Affine (spl.pre Φ n)) →
    ∀ n, Plain (spl (S := S) n) ∧ Affine (spl (S := S) n) := spl.plain_affine

end IrisTest.Stress.GuardedSbi
