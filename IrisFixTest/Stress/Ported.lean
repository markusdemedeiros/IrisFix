module

public import Iris.BI
public import IrisFix.ProofMode.Lib.Fixpoint
public import IrisFix.ProofMode.Lib.Guarded
public import IrisFix.BI.Lib.FixpointBanach

@[expose] public section
open Iris BI OFE

namespace IrisTest.Stress.Ported

local bi PROP

/-! ## Fixed and varying parameters (old `IrisTest/Fixpoint.lean`) -/

section NoBIInBody
variable {PROP : Type _} [BI PROP] {α : Type _} [OFE α]

-- The section's `[BI PROP]` is kept although the body does not mention it.
ifix zeroBad : PROP := zeroBad

example (p : PROP) : zeroBad.pre p = p := rfl
end NoBIInBody

section
variable {PROP : Type _} {α : Type _} [OFE α]

ifix zero [BI PROP] : PROP := zero

example [BI PROP] (p : PROP) : zero.pre p = p := rfl

icofix unchanged [BI PROP] (x : α) : PROP := unchanged x

example [BI PROP] (x : α) (Φ : PROP) : unchanged.pre x Φ = Φ := rfl

ifix passed [BI PROP] (x : α) : PROP :=
  let next := passed
  next x

example [BI PROP] (Φ : α → PROP) (x : α) : passed.pre Φ x = Φ x := rfl

icofix partialSwap [BI PROP] (x : α) (setting : Bool) (y : α) : PROP :=
  let next := partialSwap y setting
  next x

example [BI PROP] (setting : Bool) (Φ : α → α → PROP) (x y : α) :
    partialSwap.pre setting Φ x y = Φ y x := rfl

ifix implicitSwap [BI PROP] {x y : α} : PROP := implicitSwap (x := y) (y := x)

example [BI PROP] (x y : α) :
    implicitSwap (PROP := PROP) (x := x) (y := y) = implicitSwap (x := y) (y := x) := by
  rw [implicitSwap.unfold]

ifix indexed [BI PROP] (n : Nat) [OFE (Fin n)] (i : Fin n) : PROP := indexed n i

ifix passedPair [BI PROP] (p : α × α) : PROP := passedPair p
end

section
variable {PROP : Type _} [BI PROP] {α : Type _} [OFE α]

ifix both (x y : α) : PROP := iprop% both x y ∗ both y x

example (Φ : α → α → PROP) (x y : α) : both.pre Φ x y = iprop(Φ x y ∗ Φ y x) := rfl

ifix psig (s : (n : Nat) ×' Fin (n + 1)) (b : Bool) : PROP := iprop% ▷ psig ⟨s.1 + 1, 0⟩ (!b)

example (Φ : (n : Nat) ×' Fin (n + 1) → Bool → PROP) :
    ⊢ (□ ∀ s b, psig.pre Φ s b -∗ Φ s b) -∗ ∀ s b, psig s b -∗ Φ s b := psig.iter Φ

-- Non-recursive bodies.
icofix constant (p : PROP) : PROP := p

example (Φ : PROP → PROP) (p : PROP) : constant.pre Φ p = p := rfl

example (Φ : PROP → PROP) : ⊢ (□ ∀ p, Φ p -∗ constant.pre Φ p) -∗ ∀ p, Φ p -∗ constant p :=
  constant.coiter Φ

def base (n : Nat) (b : Bool) : PROP := iprop% ⌜n = 0 ∧ b⌝

ifix nonRecFn (n : Nat) : Bool → PROP := base n

example (Φ : Nat → Bool → PROP) (n : Nat) (b : Bool) : nonRecFn.pre Φ n b = base n b := rfl

example (Φ : Nat → Bool → PROP) :
    ⊢ (□ ∀ n b, nonRecFn.pre Φ n b -∗ Φ n b) -∗ ∀ n b, nonRecFn n b -∗ Φ n b := nonRecFn.iter Φ
end


/-! ## Section variables, universes, auto-bound implicits -/

section
variable {PROP : Type _} [BI PROP] (sameName : PROP)

-- Rejected: Lean forbids a definition named like a section variable (as for `def`).
/-- error: invalid declaration name `sameName`, there is a section variable with the same name -/
#guard_msgs in
ifix sameName : PROP := iprop% sameName ∗ emp
end

section
universe u v w
variable (PROP : Type u) [BI PROP] (α : Type v) [OFE α]

ifix lifted (x : α) : PROP :=
  let next := lifted
  let y : ULift.{w} α := ⟨x⟩
  iprop(next y.down ∗ emp)

example (Φ : α → PROP) (x : α) : lifted.pre PROP α Φ x = iprop(Φ x ∗ emp) := rfl

run_cmd do
  unless (← Lean.getConstInfo `IrisTest.Stress.Ported.lifted.pre).levelParams.contains `w do
    throwError "lost universe parameter appearing only in the body"
end

ifix inferredSwap [BI PROP] [OFE α] (x y : α) : PROP := inferredSwap y x

example [BI PROP] [OFE α] (x y : α) : inferredSwap (PROP := PROP) x y = inferredSwap.pre inferredSwap x y :=
  inferredSwap.unfold x y

/-! ## The generated lemmas -/

section
variable {PROP : Type _} [BI PROP]

ifix even (n : Nat) : PROP := iprop% ⌜n = 0⌝ ∨ ∃ m, ⌜n = m + 2⌝ ∗ even m

example (n : Nat) : even (PROP := PROP) n ⊢ ⌜n % 2 = 0⌝ := by
  iintro H
  iapply (even.iter (fun n => iprop(⌜n % 2 = 0⌝))) $$ [] %n H
  iintro !> %p Hp
  unfold even.pre
  icases Hp with (%h | ⟨%m, %h, %hm⟩) <;> ipureintro <;> omega

example (n : Nat) : Persistent (even (PROP := PROP) n) := inferInstance

icofix stream (P : PROP) : PROP := iprop% P ∗ ▷ stream P

example (P : PROP) : □ P ⊢ stream iprop(□ P) := by
  iintro #HP
  iapply (stream.coiter iprop(□ P) iprop(□ P)) $$ [] HP
  iintro !> #H
  unfold stream.pre
  isplit
  · iexact H
  · inext; iexact H

example (P Φ : PROP) : ⊢ □ (Φ -∗ stream.pre P (stream P)) -∗ Φ -∗ stream P :=
  stream.paco P Φ (stream P) ((stream.unfold_mp P).trans or_intro_r)

example (P : PROP) : stream.pre P (stream P) ⊢ stream P := stream.unfold_mpr P

ifix nat (n : Nat) : PROP := iprop% ⌜n = 0⌝ ∨ ∃ m, ⌜n = m + 1⌝ ∗ nat m
ifix nat' (n : Nat) : PROP := iprop% ⌜n = 0⌝ ∨ ∃ m, ⌜n = m + 1⌝ ∗ nat' m

example (Φ : Nat → PROP) : ⊢ (□ ∀ n, nat.pre nat n -∗ Φ n) -∗ ∀ n, nat n -∗ Φ n :=
  nat.ind_wf Φ nat fun n => and_elim_r.trans (nat.unfold n).to_bi.2

example (n : Nat) : nat (PROP := PROP) n ⊢ nat' n := by
  iintro H
  iapply (nat.strong_mono nat'.pre nat' fun n => (nat'.unfold n).to_bi.2) $$ [] %n H
  iintro !> %Φ %m HΦ
  iexact HΦ

example [BIAffine PROP] (n : Nat) : Affine (nat (PROP := PROP) n) := inferInstance

-- No `eq_lfp` (known): the old `⟨_, nat.eq_lfp⟩` has no counterpart.
/-- error: Unknown constant `IrisTest.Stress.Ported.nat.eq_lfp` -/
#guard_msgs (error, substring := true) in
open MonotoneFixpoint in
example : ∃ h, nat (PROP := PROP) = Lean.Order.fix nat.pre h := ⟨_, nat.eq_lfp⟩

ifix vec (n : Nat) (v : Fin n → Nat) : PROP :=
  iprop(⌜∀ i, v i = 0⌝ ∨ ∃ m, ∃ w : Fin m → Nat, ⌜n = m + 1⌝ ∗ vec m w)

example (Φ : (n : Nat) → (Fin n → Nat) → PROP) :
    ⊢ (□ ∀ n v, vec.pre Φ n v -∗ Φ n v) -∗ ∀ n v, vec n v -∗ Φ n v := vec.iter Φ

ifix swapNe {α : Type _} [OFE α] (x y : α) : PROP := iprop% ▷ swapNe y x

example {α : Type _} [OFE α] {n : Nat} {x x' y y' : α} (hx : x ≡{n}≡ x') (hy : y ≡{n}≡ y') :
    swapNe (PROP := PROP) x y ≡{n}≡ swapNe x' y' :=
  swapNe.ne (fun _ _ hf x x' hx y y' hy => later_ne.ne (hf y y' hy x x' hx)) x x' hx y y' hy
end

/-! ## Default tactics and `imono` -/

section
variable {PROP : Type _} [BI PROP]

elab "logged_imono" : tactic => do
  Lean.logInfo "monotone_by ran"
  Lean.Elab.Tactic.evalTactic (← `(tactic| imono))

-- Improvement over the old design: the tactic runs once (the old ran it twice).
/-- info: monotone_by ran -/
#guard_msgs in
ifix once (n : Nat) : PROP := iprop% ⌜n = 0⌝ ∨ once (n + 1)
monotone_by logged_imono

-- Rejected: the body is not monotone (`bad` left of a wand). One error, and no laws.
/--
error: imono: not monotone, or not covered by an @[imono] rule
PROP : Type u_1
inst✝ : BI PROP
n : Nat
Φ✝ Ψ✝ : PROP
⊢ ⊢ □ (Φ✝ -∗ Ψ✝) -∗ Ψ✝ -∗ Φ✝
-/
#guard_msgs in
ifix bad (n : Nat) : PROP := iprop% bad n -∗ False

run_cmd do
  if (← Lean.getEnv).contains `IrisTest.Stress.Ported.bad.iter then
    throwError "no laws expected for a failed definition"

-- Old feature with no equivalent: the option `iris.fixpoint.monotoneDefault`, and the
-- `ifix_monotone_default` extension point (`imono` is hard-coded; extend it with `@[imono]`).
/-- error: Unknown option `iris.fixpoint.monotoneDefault` -/
#guard_msgs (error, substring := true) in
set_option iris.fixpoint.monotoneDefault false in
ifix noDefault (n : Nat) : PROP := iprop% ⌜n = 0⌝ ∨ noDefault n

def later' (X : PROP) : PROP := iprop% ▷ X
def twice (Φ : Nat → PROP) (n : Nat) : PROP := later' (later' (Φ n))

example : BIMono (PROP := PROP) twice := by imono

def bigSep (Φ : List Nat → PROP) : List Nat → PROP
  | [] => iprop(emp)
  | _ :: xs => iprop(Φ xs ∗ bigSep Φ xs)

/-- error: imono: no rule for IrisTest.Stress.Ported.bigSep, after unfolding it once -/
#guard_msgs (error, substring := true) in
example : BIMono (fun (Φ : List Nat → PROP) l => bigSep Φ l) := by imono

example : BIMono (fun (Φ : Nat → PROP) n => if n = 0 then iprop(emp) else Φ (n - 1)) := by imono

/-- error: imono: expected a monotonicity goal -/
#guard_msgs (error, substring := true) in
example : True := by imono
end

/-! ## Names and attributes -/

namespace Names
variable {PROP : Type _} [BI PROP]

-- A parameter named like the definition (it shadows the recursive call).
ifix self (self : Nat) : PROP :=
  iprop(⌜self = 0⌝ ∨ ▷ IrisTest.Stress.Ported.Names.self (self + 1))

example (n : Nat) : self (PROP := PROP) n = self.pre self n := self.unfold n

protected ifix prot (n : Nat) : PROP := iprop% ⌜n = 0⌝ ∨ ▷ Names.prot (n + 1)

example (n : Nat) : Names.prot (PROP := PROP) n = Names.prot.pre Names.prot n := Names.prot.unfold n

set_option linter.iris.dupNamespace false in
def Names.clash : Nat := 0

ifix clash (n : Nat) : PROP := iprop% ▷ clash (n + 1)

example (n : Nat) : clash (PROP := PROP) n = clash.pre clash n := clash.unfold n

ifix _root_.rootedFix (n : Nat) : PROP := iprop% ▷ rootedFix (n + 1)

example (n : Nat) : _root_.rootedFix (PROP := PROP) n = _root_.rootedFix.pre rootedFix n :=
  _root_.rootedFix.unfold n

ifix Sub.nested (n : Nat) : PROP := iprop% ▷ Sub.nested (n + 1)

example (n : Nat) : Sub.nested (PROP := PROP) n = Sub.nested.pre Sub.nested n := Sub.nested.unfold n

@[semireducible] ifix semireducibleFix (n : Nat) : PROP := iprop% ▷ semireducibleFix (n + 1)

@[local simp] ifix localSimp (n : Nat) : PROP := iprop% ⌜n = 0⌝ ∗ emp

example (n : Nat) : localSimp (PROP := PROP) n = localSimp.pre localSimp n := localSimp.unfold n
end Names

/-! ## `iguarded` (old `IrisTest/FixpointGuarded.lean`) -/

namespace Guarded
variable {PROP : Type _} [BI PROP] [BILaterContractive PROP] [Inhabited PROP]

-- A type without a COFE gives one error (the old message was "must be a COFE with a default point").
/--
error: failed to synthesize instance of type class
  OFE (Nat → Nat)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs (error, drop warning) in
iguarded notCOFE (n : Nat) : Nat := notCOFE n
contractive_by sorry

iguarded flip (b : Bool) : PROP := iprop% ▷ flip (!b) -∗ False
contractive_by
  intros n Φ Ψ h b
  unfold flip.pre
  exact wand_ne.ne (Contractive.distLater_dist (fun m hm => h m hm (!b))) .rfl

example (b : Bool) : flip (PROP := PROP) b = iprop(▷ flip (!b) -∗ False) := flip.unfold b
-- `eq_fixpoint` is now unapplied: the old `flip.eq_fixpoint b` needs `congrFun`.
example (b : Bool) : flip (PROP := PROP) b = fixpoint flip.pre b := congrFun flip.eq_fixpoint b

iguarded g0 : PROP := iprop% ▷ g0
contractive_by intros k x y h; unfold g0.pre; exact Contractive.distLater_dist h

example : Persistent (g0 (PROP := PROP)) :=
  g0.persistent fun Φ _ => by unfold g0.pre; infer_instance

iguarded g2 (b : Bool) (n : Nat) : PROP := iprop% ▷ g2 (!b) (n + 1)
contractive_by
  intros k Φ Ψ h b n; unfold g2.pre; exact Contractive.distLater_dist (fun m hm => h m hm _ _)

example (b : Bool) (n : Nat) : Persistent (g2 (PROP := PROP) b n) :=
  g2.persistent (fun Φ h b n => by unfold g2.pre; have := h (!b) (n + 1); infer_instance) b n

iguarded dependent (n : Nat) (i : Fin n) : PROP := iprop% ▷ dependent n i
contractive_by
  intros k Φ Ψ h n i; unfold dependent.pre
  exact Contractive.distLater_dist (fun m hm => h m hm _ _)

example (n : Nat) (i : Fin n) : dependent (PROP := PROP) n i = dependent.pre dependent n i :=
  dependent.unfold n i

iguarded gf (n : Nat) : Bool → PROP := fun b => iprop(▷ gf (n + 1) b)
contractive_by
  intros k Φ Ψ h n b; unfold gf.pre; exact Contractive.distLater_dist (fun m hm => h m hm _ _)

example (n : Nat) (b : Bool) : Persistent (gf (PROP := PROP) n b) :=
  gf.persistent (fun Φ h n b => by unfold gf.pre; have := h (n + 1) b; infer_instance) n b

protected iguarded prot (n : Nat) : PROP := iprop% ▷ prot (n + 1)
contractive_by
  intros k Φ Ψ h n; unfold Guarded.prot.pre
  exact Contractive.distLater_dist (fun m hm => h m hm _)

example (n : Nat) : Guarded.prot (PROP := PROP) n = Guarded.prot.pre Guarded.prot n :=
  Guarded.prot.unfold n

noncomputable def ncProp : PROP := Classical.choice ⟨iprop(emp)⟩

noncomputable iguarded nc (n : Nat) : PROP := iprop% ▷ (nc (n + 1) ∗ ncProp)
contractive_by
  intros k a b h x; unfold nc.pre
  exact Contractive.distLater_dist (fun m hm => sep_ne.ne (h m hm _) .rfl)

example (n : Nat) : nc (PROP := PROP) n = nc.pre nc n := nc.unfold n

iguarded withInst [Inhabited Nat] (n : Nat) : PROP := iprop% ▷ withInst (n + 1)
contractive_by
  intros k Φ Ψ h i n; unfold withInst.pre
  exact Contractive.distLater_dist (fun m hm => h m hm _ _)

example [Inhabited Nat] (n : Nat) : withInst (PROP := PROP) n = withInst.pre withInst n :=
  withInst.unfold n

iguarded impl {n : Nat} : PROP := iprop% ▷ impl (n := n + 1)
contractive_by
  intros k Φ Ψ h n; unfold impl.pre
  exact Contractive.distLater_dist (fun m hm => h m hm _)

example (n : Nat) : impl (PROP := PROP) (n := n) = impl.pre (fun {m} => impl (n := m)) (n := n) :=
  impl.unfold

iguarded autoBound [OFE α] (x : α) : PROP := iprop% ▷ autoBound x
contractive_by
  intros k Φ Ψ h i x; unfold autoBound.pre
  exact Contractive.distLater_dist (fun m hm => h m hm _ _)

example {α : Type} [OFE α] (x : α) : autoBound (PROP := PROP) x = autoBound.pre autoBound x :=
  autoBound.unfold x

section
variable {α : Type} [Inhabited α]

iguarded sectionInh (a : α) : PROP := iprop% ▷ (⌜a = default⌝ ∗ sectionInh a)
contractive_by
  intros k Φ Ψ h a; unfold sectionInh.pre
  exact Contractive.distLater_dist (fun m hm => sep_ne.ne .rfl (h m hm _))

example (a : α) : Persistent (sectionInh (PROP := PROP) a) :=
  sectionInh.persistent (fun Φ h a => by unfold sectionInh.pre; have := h a; infer_instance) a
end

iguarded hole (_ : Nat) (n : Nat) : PROP := iprop% ▷ hole 0 n
contractive_by
  intros k Φ Ψ h i n; unfold hole.pre; exact Contractive.distLater_dist (fun m hm => h m hm _ _)

-- Rejected: every parameter of `iguarded` varies, so a default value has no meaning.
/-- error: iguarded: parameters cannot have default values -/
#guard_msgs in
iguarded withDefault (n : Nat := 3) : PROP := iprop% ▷ withDefault n
contractive_by
  intros k Φ Ψ h n; unfold withDefault.pre
  exact Contractive.distLater_dist (fun m hm => h m hm _)

iguarded Foo.bar (n : Nat) : PROP := iprop% ▷ Foo.bar n
contractive_by
  intros k Φ Ψ h n; unfold Foo.bar.pre; exact Contractive.distLater_dist (fun m hm => h m hm _)

example (n : Nat) : Foo.bar (PROP := PROP) n = Foo.bar.pre Foo.bar n := Foo.bar.unfold n

section
variable (m : Nat)

-- An explicit section variable in the body becomes a fixed parameter.
iguarded viaProj (_n : Nat) : PROP := iprop% ▷ viaProj m.succ
contractive_by
  intros k Φ Ψ h n; unfold viaProj.pre; exact Contractive.distLater_dist (fun m hm => h m hm _)

example (n : Nat) : viaProj (PROP := PROP) m n = viaProj.pre m (viaProj m) n := viaProj.unfold m n

iguarded shadowed (m : Nat) : PROP := iprop% ▷ shadowed (m + 1)
contractive_by
  intros k Φ Ψ h m; unfold shadowed.pre; exact Contractive.distLater_dist (fun m hm => h m hm _)
end
end Guarded

/-! ## No `sorry` or unexpected axioms -/

run_cmd do
  let pre := `IrisTest.Stress.Ported
  let decls := #[`zero, `zeroBad, `passed, `both, `partialSwap, `implicitSwap, `indexed, `psig,
      `constant, `nonRecFn, `lifted, `even, `stream, `nat, `vec, `swapNe, `inferredSwap,
      `Names.self, `Names.prot, `Names.clash, `Names.Sub.nested, `Names.localSimp,
      `Guarded.flip, `Guarded.g0, `Guarded.g2, `Guarded.dependent, `Guarded.gf, `Guarded.prot,
      `Guarded.nc, `Guarded.withInst, `Guarded.impl, `Guarded.autoBound, `Guarded.sectionInh,
      `Guarded.hole, `Guarded.Foo.bar, `Guarded.viaProj, `Guarded.shadowed].map (pre ++ ·)
  for decl in decls.push `rootedFix do
    unless (← Lean.getEnv).contains decl do throwError "missing {decl}"
    for suffix in #[Lean.Name.anonymous, `pre, `pre_mono, `pre.contractive, `unfold, `unfold_mp,
        `unfold_mpr, `iter, `ind, `ind_wf, `coiter, `coind, `paco, `strong_mono, `affine,
        `absorbing, `persistent_affine, `persistent_absorbing, `ne, `eq_fixpoint, `persistent,
        `plain] do
      let name := decl ++ suffix
      unless (← Lean.getEnv).contains name do continue
      for axiomName in (← Lean.collectAxioms name) do
        unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
          throwError "unexpected axiom {axiomName} in {name}"

end IrisTest.Stress.Ported
