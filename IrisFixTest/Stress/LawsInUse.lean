module

public import Iris.BI
public import IrisFix.ProofMode.Lib.Fixpoint
public import IrisFix.ProofMode.Lib.Guarded

@[expose] public section
open Iris BI OFE

namespace IrisTest.Stress.LawsInUse

local bi PROP

variable {PROP : Type _} [BI PROP]

ifix even (n : Nat) : PROP := iprop% ⌜n = 0⌝ ∨ ∃ m, ⌜n = m + 2⌝ ∗ even m

-- fold with unfold
theorem even_zero : ⊢ even (PROP := PROP) 0 := by
  rw [even.unfold]
  ileft; ipureintro; rfl

theorem even_ss (n : Nat) : even (PROP := PROP) n ⊢ even (n + 2) := by
  iintro H
  rw [even.unfold (n + 2)]
  iright
  iexists n
  isplitr
  · ipureintro; rfl
  · iexact H

-- unfold in proof mode, in a hypothesis
theorem even_inv (n : Nat) : even (PROP := PROP) (n + 2) ⊢ even n := by
  rw [even.unfold]
  iintro (%h | ⟨%m, %hm, H⟩)
  · omega
  · have : m = n := by omega
    subst this; iexact H

-- iter
theorem even_mod (n : Nat) : even (PROP := PROP) n ⊢ ⌜n % 2 = 0⌝ := by
  iintro H
  iapply (even.iter (fun n => iprop(⌜n % 2 = 0⌝)))
  · iintro !> %k (%hk | ⟨%m, %hm, %ih⟩)
    · ipureintro; omega
    · ipureintro; omega
  · iexact H

-- iter via ispecialize/ihave
theorem even_mod' (n : Nat) : even (PROP := PROP) n ⊢ ⌜n % 2 = 0⌝ := by
  iintro H
  ihave Hit := even.iter (PROP := PROP) (fun n => iprop(⌜n % 2 = 0⌝))
  ispecialize Hit $$ []
  · iintro !> %k (%hk | ⟨%m, %hm, %ih⟩) <;> ipureintro <;> omega
  · iapply Hit $$ H

-- ind (strong)
theorem even_ind_use (n : Nat) : even (PROP := PROP) n ⊢ even (n + 4) := by
  iintro H
  iapply (even.ind (fun n => iprop(even (n + 4)))) $$ [] H
  iintro !> %k (%hk | ⟨%m, %hm, ⟨Hih, He⟩⟩)
  · subst hk; iapply even_ss; iapply even_ss; iapply even_zero
  · subst hm; iapply even_ss; iexact Hih

-- persistence via the generated instance, used in proof mode
example (n : Nat) : Persistent (even (PROP := PROP) n) := inferInstance
example (n : Nat) : even (PROP := PROP) n ⊢ even n ∗ even n := by
  iintro #H
  isplitl
  · iexact H
  · iexact H

-- ind_wf, with W := even
theorem even_ind_wf_use (n : Nat) : even (PROP := PROP) n ⊢ ⌜n % 2 = 0 ∨ True⌝ := by
  iintro H
  iapply (even.ind_wf (fun n => iprop(⌜n % 2 = 0 ∨ True⌝)) even (fun k => ?_)) $$ [] H
  · iintro ⟨_, H⟩; rw [even.unfold]; iexact H
  · iintro !> %k _; ipureintro; exact .inr trivial

-- strong_mono: even n ⊢ (True-wrapped) even
theorem even_strong_mono (n : Nat) : even (PROP := PROP) n ⊢ even n := by
  iintro H
  iapply (even.strong_mono (fun Φ n => even.pre Φ n) even (fun k => by rw [even.unfold])) $$ [] H
  iintro !> %Φ %k H; iexact H

-- pre_mono in a proof
example (n : Nat) (Φ Ψ : Nat → PROP) (h : ∀ n, Φ n ⊢ Ψ n) : even.pre Φ n ⊢ even.pre Ψ n := by
  iintro H
  iapply (even.pre_mono Φ Ψ) $$ [] H
  iintro !> %k Hk; iapply h; iexact Hk

/-! ## Mutual recursion via a Bool flag -/

ifix eo (b : Bool) (n : Nat) : PROP :=
  if b then iprop(⌜n = 0⌝ ∨ ∃ m, ⌜n = m + 1⌝ ∗ eo false m)
  else iprop(∃ m, ⌜n = m + 1⌝ ∗ eo true m)

#check @eo.unfold
#check @eo.iter
#check @eo.affine

theorem eo_true_zero : ⊢ eo (PROP := PROP) true 0 := by
  rw [eo.unfold]; simp only [eo.pre, ite_true]; ileft; ipureintro; trivial

theorem eo_sound (b : Bool) (n : Nat) : eo (PROP := PROP) b n ⊢ ⌜decide (n % 2 = 0) = b⌝ := by
  iintro H
  iapply (eo.iter (fun b n => iprop(⌜decide (n % 2 = 0) = b⌝))) $$ [] H
  iintro !> %b %k Hk
  cases b
  · simp only [eo.pre, Bool.false_eq_true, ite_false]
    icases Hk with ⟨%m, %hm, %ih⟩
    ipureintro; simp at ih ⊢; omega
  · simp only [eo.pre, ite_true]
    icases Hk with (%hk | ⟨%m, %hm, %ih⟩)
    · ipureintro; simp; omega
    · ipureintro; simp at ih ⊢; omega


-- Limitation: instances of a flag-indexed (`if`) definition never fire, even at a concrete flag:
-- the generated instance needs its hypothesis at every flag, and `if b` blocks instance search.
/--
error: failed to synthesize instance of type class
  Persistent (eo true 0)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : Persistent (eo (PROP := PROP) true 0) := inferInstance
-- The law, with its hypothesis proved by cases, does work.
example : Persistent (eo (PROP := PROP) true 0) :=
  have : ∀ b n, Absorbing (eo (PROP := PROP) b n) := eo.absorbing (h := fun b n => by
    cases b <;> simp only [eo.pre, Bool.false_eq_true, ite_false, ite_true] <;> infer_instance)
  eo.persistent_absorbing (hP := fun b n => by
    cases b <;> simp only [eo.pre, Bool.false_eq_true, ite_false, ite_true] <;> infer_instance) true 0

/-! ## Mutual recursion via `match` on a Bool -/

ifix eo2 (b : Bool) (n : Nat) : PROP :=
  match b with
  | true => iprop(⌜n = 0⌝ ∨ ∃ m, ⌜n = m + 1⌝ ∗ eo2 false m)
  | false => iprop(∃ m, ⌜n = m + 1⌝ ∗ eo2 true m)

#check @eo2.unfold
-- Limitation: as for `eo`, the `match b` blocks the generated instance.
/--
error: failed to synthesize instance of type class
  Persistent (eo2 true 0)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : Persistent (eo2 (PROP := PROP) true 0) := inferInstance

-- A user instance about `eo2.pre` is found at its own statement.
instance eo2_pre_absorbing (b : Bool) (n : Nat) :
    Absorbing (eo2.pre (PROP := PROP) (fun b n => iprop(True -∗ eo2 b n)) b n) := by
  cases b <;> simp only [eo2.pre] <;> infer_instance
example (b : Bool) (n : Nat) :
    Absorbing (eo2.pre (PROP := PROP) (fun b n => iprop(True -∗ eo2 b n)) b n) := inferInstance

/-! ## List segment, with an abstract points-to as fixed parameter -/

ifix lseg (pt : Nat → Nat → Nat → PROP) (p q : Nat) (l : List Nat) : PROP :=
  match l with
  | [] => iprop(⌜p = q⌝)
  | x :: xs => iprop(∃ p', pt p x p' ∗ lseg pt p' q xs)

#check @lseg.unfold
#check @lseg.iter
#check @lseg.ind

theorem lseg_nil (pt : Nat → Nat → Nat → PROP) (p : Nat) : ⊢ lseg pt p p [] := by
  rw [lseg.unfold]; ipureintro; rfl

theorem lseg_cons (pt : Nat → Nat → Nat → PROP) (p p' q x : Nat) (xs : List Nat) :
    pt p x p' ∗ lseg pt p' q xs ⊢ lseg pt p q (x :: xs) := by
  iintro ⟨Hpt, Hl⟩
  rw [lseg.unfold pt p q (x :: xs)]
  iexists p'
  iframe

theorem lseg_app [BIAffine PROP] (pt : Nat → Nat → Nat → PROP) (p q r : Nat) (xs ys : List Nat) :
    lseg pt p q xs ∗ lseg pt q r ys ⊢ lseg pt p r (xs ++ ys) := by
  iintro ⟨H1, H2⟩
  irevert H2
  iapply (lseg.iter pt q (fun p xs => iprop(lseg pt q r ys -∗ lseg pt p r (xs ++ ys)))) $$ [] H1
  iintro !> %p %xs Hxs H2
  cases xs with
  | nil =>
    simp only [lseg.pre]
    icases Hxs with %h
    subst h; simp only [List.nil_append]; iexact H2
  | cons x xs =>
    simp only [lseg.pre, List.cons_append]
    icases Hxs with ⟨%p', Hpt, Hih⟩
    iapply lseg_cons
    iframe
    iapply Hih $$ H2

-- fixed parameter in the middle, after a varying one
ifix lseg2 (p : Nat) (pt : Nat → Nat → Nat → PROP) (l : List Nat) (q : Nat) : PROP :=
  match l with
  | [] => iprop(⌜p = q⌝)
  | x :: xs => iprop(∃ p', pt p x p' ∗ lseg2 p' pt xs q)
#check @lseg2.pre
#check @lseg2.unfold
#check @lseg2.iter
theorem lseg2_len (pt : Nat → Nat → Nat → PROP) (p q : Nat) (l : List Nat) :
    lseg2 p pt l q ⊢ ⌜l = [] → p = q⌝ := by
  iintro H
  iapply (lseg2.iter pt q (fun p l => iprop(⌜l = [] → p = q⌝))) $$ [] H
  iintro !> %p %l Hl
  cases l with
  | nil => simp only [lseg2.pre]; icases Hl with %h; ipureintro; intro; exact h
  | cons x xs => ipureintro; intro h; cases h

-- Limitation: the generated instance needs `Absorbing (lseg.pre .. p l)` at every `l`, which
-- the `match` on `l` blocks: a list segment of persistent cells is never found absorbing.
/--
error: failed to synthesize instance of type class
  Absorbing (lseg pt p q l)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example (pt : Nat → Nat → Nat → PROP) [∀ a b c, Persistent (pt a b c)] (p q : Nat) (l : List Nat) :
    Absorbing (lseg pt p q l) := inferInstance
example (pt : Nat → Nat → Nat → PROP) [∀ a b c, Persistent (pt a b c)] (p q : Nat) (l : List Nat) :
    Absorbing (lseg pt p q l) :=
  lseg.absorbing pt q (h := fun p l => by cases l <;> simp only [lseg.pre] <;> infer_instance) p l
example (pt : Nat → Nat → Nat → PROP) [∀ a b c, Persistent (pt a b c)] (p q : Nat) (l : List Nat) :
    Persistent (lseg pt p q l) :=
  have : ∀ p l, Absorbing (lseg pt p q l) := 
    lseg.absorbing pt q (h := fun p l => by cases l <;> simp only [lseg.pre] <;> infer_instance)
  lseg.persistent_absorbing pt q (hP := fun p l => by cases l <;> simp only [lseg.pre] <;> infer_instance) p l


/-! ## Coinductive streams -/

icofix stream (P : Nat → PROP) (n : Nat) : PROP := iprop% P n ∗ ▷ stream P (n + 1)

#check @stream.coiter
#check @stream.paco

-- `rw [name.pre]` and the equation lemmas `name.pre.eq_1` / `name.pre.eq_def` work.
example (P Φ : Nat → PROP) (n : Nat) : stream.pre P Φ n = iprop(P n ∗ ▷ Φ (n + 1)) := by
  rw [stream.pre]

example (Φ : Nat → PROP) (n : Nat) :
    even.pre Φ n = iprop(⌜n = 0⌝ ∨ ∃ m, ⌜n = m + 2⌝ ∗ Φ m) := even.pre.eq_def Φ n
example (Φ : Nat → PROP) (n : Nat) :
    even.pre Φ n = iprop(⌜n = 0⌝ ∨ ∃ m, ⌜n = m + 2⌝ ∗ Φ m) := even.pre.eq_1 Φ n

-- `unfold`, `simp only`, `dsimp only`, `delta` and `rfl` do work.
example (P Φ : Nat → PROP) (n : Nat) : stream.pre P Φ n = iprop(P n ∗ ▷ Φ (n + 1)) := by
  unfold stream.pre; rfl
example (P Φ : Nat → PROP) (n : Nat) : stream.pre P Φ n = iprop(P n ∗ ▷ Φ (n + 1)) := by
  simp only [stream.pre]
example (P Φ : Nat → PROP) (n : Nat) : stream.pre P Φ n = iprop(P n ∗ ▷ Φ (n + 1)) := rfl

theorem stream_of_all' (P : Nat → PROP) [∀ n, Persistent (P n)] (n : Nat) :
    (□ ∀ k, P k) ⊢ stream P n := by
  iintro #HP
  iapply (stream.coiter P (fun _ => iprop(□ ∀ k, P k))) $$ [] HP
  iintro !> %k #H
  isplitl
  · iapply H
  · inext; iexact H

-- coind: use the coinductive hypothesis disjunct
theorem stream_coind_use (P : Nat → PROP) [∀ n, Persistent (P n)] (n : Nat) :
    (□ ∀ k, P k) ⊢ stream P n := by
  iintro #HP
  iapply (stream.coind P (fun _ => iprop(□ ∀ k, P k))) $$ [] HP
  iintro !> %k #H
  isplitl
  · iapply H
  · inext; ileft; iexact H

-- unfold on a stream hypothesis
theorem stream_head (P : Nat → PROP) (n : Nat) : stream P n ⊢ P n ∗ ▷ stream P (n + 1) := by
  rw [stream.unfold]

theorem stream_tail (P : Nat → PROP) [∀ n, Absorbing (P n)] (n : Nat) :
    stream P n ⊢ ▷ stream P (n + 1) := by
  iintro H
  rw [stream.unfold]
  icases H with ⟨-, H⟩
  iexact H

-- paco, with W := stream
theorem stream_paco_use (P : Nat → PROP) (n : Nat) : stream P n ⊢ stream P n := by
  iintro H
  iapply (stream.paco P (stream P) (stream P) (fun k => by iintro H; iright; rw [stream.unfold]; iexact H)) $$ [] H
  iintro !> %k H
  rw [stream.unfold]; iexact H

-- absorbing instance
example (P : Nat → PROP) [∀ n, Absorbing (P n)] (n : Nat) : Absorbing (stream P n) := inferInstance
example (P : Nat → PROP) [∀ n, Absorbing (P n)] (n : Nat) : stream P n ∗ P 0 ⊢ stream P n := by
  iintro ⟨H, -⟩; iexact H

-- pre_mono for a gfp
example (P : Nat → PROP) (Φ Ψ : Nat → PROP) (h : ∀ n, Φ n ⊢ Ψ n) (n : Nat) :
    stream.pre P Φ n ⊢ stream.pre P Ψ n := by
  iintro H
  iapply (stream.pre_mono P Ψ Φ) $$ [] H
  iintro !> %k Hk; iapply h; iexact Hk

-- strong_mono for a gfp
#check @stream.strong_mono

/-! ## Zero varying parameters -/

icofix forever (P : PROP) : PROP := iprop% P ∗ ▷ forever P
#check @forever.unfold
#check @forever.coiter
#check @forever.coind
#check @forever.paco
#check @forever.absorbing
theorem forever_intro (P : PROP) [Persistent P] : □ P ⊢ forever P := by
  iintro #H
  iapply (forever.coiter P iprop(□ P)) $$ [] H
  iintro !> #H
  isplitl
  · iexact H
  · inext; iexact H

ifix spin : PROP := iprop% ▷ spin
#check @spin.unfold
#check @spin.iter
#check @spin.affine
example : Persistent (spin (PROP := PROP)) := inferInstance
example : Absorbing (spin (PROP := PROP)) := inferInstance

-- `spin.iter` at `Φ := emp ∧ True`... any `Φ` with `▷ Φ ⊢ Φ`.
theorem spin_iter_use (Φ : PROP) (h : ▷ Φ ⊢ Φ) : spin (PROP := PROP) ⊢ Φ := by
  iintro H
  iapply (spin.iter (PROP := PROP) Φ) $$ [] H
  iintro !> H
  iapply h; iexact H

/-! ## Dependent and implicit varying parameters -/

ifix vec {n : Nat} (v : Fin n → Nat) : PROP := iprop% ⌜n = 0⌝ ∨ ∃ (m : Nat) (h : n = m + 1), vec (n := m) (fun i => v (h ▸ i.succ))
#check @vec.pre
#check @vec.unfold
#check @vec.iter

ifix finP (n : Nat) (i : Fin n) : PROP := iprop% ⌜i.val = 0⌝ ∨ ∃ (j : Fin n), ⌜j.val + 1 = i.val⌝ ∗ finP n j
#check @finP.unfold
#check @finP.iter
#check @finP.ind
example (n : Nat) (i : Fin n) : Persistent (finP (PROP := PROP) n i) := inferInstance

theorem finP_all (n : Nat) (i : Fin n) : ⊢ finP (PROP := PROP) n i := by
  obtain ⟨k, hk⟩ := i
  induction k with
  | zero => rw [finP.unfold]; ileft; ipureintro; rfl
  | succ k ih =>
    rw [finP.unfold]; iright; iexists ⟨k, by omega⟩
    isplitr
    · ipureintro; rfl
    · iapply ih


/-! ## `ne` -/

section
variable {α : Type _} [OFE α]

-- BUG(usability): an `[OFE α]` section variable is dropped by `def` when unused in the body, so no
-- `ne` is emitted, silently.
ifix walkS (x : α) (k : Nat) (y : α) : PROP := iprop% ▷ walkS y k x
/-- error: Unknown constant `IrisTest.Stress.LawsInUse.walkS.ne` -/
#guard_msgs in #check @walkS.ne
end

section
variable {α : Type _}

ifix walk [OFE α] (x : α) (k : Nat) (y : α) : PROP := iprop% ▷ walk y k x
#check @walk.ne

example [OFE α] {n : Nat} (k : Nat) {x x' y y' : α} (hx : x ≡{n}≡ x') (hy : y ≡{n}≡ y') :
    walk (PROP := PROP) x k y ≡{n}≡ walk x' k y' :=
  walk.ne k (fun _ _ hf x x' hx y y' hy => later_ne.ne (hf y y' hy x x' hx)) x x' hx y y' hy

-- `NonExpansive` from `ne`
example [OFE α] (k : Nat) (y : α) : NonExpansive (fun x => walk (PROP := PROP) x k y) :=
  ⟨fun {_} x x' hx => walk.ne k (fun _ _ hf x x' hx y y' hy => later_ne.ne (hf y y' hy x x' hx))
    x x' hx y y .rfl⟩

-- a fixed OFE argument, varying Nat
ifix chainP [OFE α] (x : α) (k : Nat) : PROP := iprop% ⌜k = 0⌝ ∨ ▷ chainP x (k - 1)
#check @chainP.pre
-- No `ne` in a fixed OFE argument: only the varying arguments are covered.
/-- error: Unknown constant `IrisTest.Stress.LawsInUse.chainP.ne` -/
#guard_msgs in #check @chainP.ne
end

/-! ## Persistent, via the instance, in proof mode -/

ifix reach (R : Nat → Nat → Prop) (a b : Nat) : PROP :=
  iprop(⌜a = b⌝ ∨ ∃ c, ⌜R a c⌝ ∗ reach R c b)
#check @reach.unfold
#check @reach.iter

example [BIAffine PROP] (R : Nat → Nat → Prop) (a b : Nat) : reach (PROP := PROP) R a b ⊢ □ reach R a b := by
  iintro #H; imodintro; iexact H

theorem reach_trans [BIAffine PROP] (R : Nat → Nat → Prop) (a b c : Nat) :
    reach (PROP := PROP) R a b ∗ reach R b c ⊢ reach R a c := by
  iintro ⟨H1, H2⟩
  irevert H2
  iapply (reach.iter R b (fun a => iprop(reach R b c -∗ reach R a c))) $$ [] H1
  iintro !> %a (%h | ⟨%d, %hd, Hih⟩) H2
  · subst h; iexact H2
  · rw [reach.unfold R a c]; iright; iexists d; isplitr
    · ipureintro; exact hd
    · iapply Hih $$ H2

-- iter with every parameter generalized: impossible because b is fixed.
#check @reach.ind_wf


/-! ## `iapply` with the law, inferring the motive -/

theorem even_mod_infer : ⊢@{PROP} ∀ n, even n -∗ ⌜n % 2 = 0⌝ := by
  iapply even.iter
  iintro !> %k (%hk | ⟨%m, %hm, %ih⟩) <;> ipureintro <;> omega

theorem even_mod_named (n : Nat) : even (PROP := PROP) n ⊢ ⌜n % 2 = 0⌝ := by
  iintro H
  ihave Hit := even.iter (Φ := fun n => iprop(⌜n % 2 = 0⌝))
  ispecialize Hit $$ [] %n H
  · iintro !> %k (%hk | ⟨%m, %hm, %ih⟩) <;> ipureintro <;> omega
  · iexact Hit

/-! ## Instances: affine/persistent routes -/

ifix pa (n : Nat) : PROP := iprop% <affine> ⌜n = 0⌝ ∨ ∃ m, <affine> ⌜n = m + 1⌝ ∗ pa m
example (n : Nat) : Affine (pa (PROP := PROP) n) := inferInstance
example (n : Nat) : Persistent (pa (PROP := PROP) n) := inferInstance
example (n : Nat) : pa (PROP := PROP) n ⊢ pa n ∗ pa n := by
  iintro #H; isplitl <;> iexact H

ifix np (P : PROP) (n : Nat) : PROP := iprop% P ∗ np P n
/--
error: failed to synthesize instance of type class
  Persistent (np P n)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example (P : PROP) (n : Nat) : Persistent (np P n) := inferInstance
example (P : PROP) [Persistent P] (n : Nat) : Persistent (np P n) := inferInstance

-- A body that uses no BI operation still gets the `[BI PROP]` section variable (`local bi`).
ifix selfloop (n : Nat) : PROP := iprop% selfloop n
example (n : Nat) : Persistent (selfloop (PROP := PROP) n) := inferInstance
example (n : Nat) : selfloop (PROP := PROP) n = selfloop.pre n (selfloop n) := selfloop.unfold n

-- With the instance in the binders.
ifix selfloop' [BI PROP] (n : Nat) : PROP := iprop% selfloop' n
example (n : Nat) : Persistent (selfloop' (PROP := PROP) n) := inferInstance
example (n : Nat) : Affine (selfloop' (PROP := PROP) n) := inferInstance

/-! ## Binder names that clash with the law's own names -/

ifix clash (Φ : PROP) (W : Nat) : PROP := iprop% Φ ∗ clash Φ (W + 1)
#check @clash.iter
#check @clash.ind_wf
-- named argument `Φ` refers to the fixed parameter, the motive is primed: `Φ'`
#check clash.iter (PROP := PROP) (Φ := iprop(True)) (Φ' := fun _ => iprop(True))

ifix clash2 (Φ : Nat) (x : Nat) : PROP := iprop% ⌜Φ = x⌝ ∨ clash2 (Φ + 1) x
#check @clash2.iter
#check @clash2.strong_mono
#check @clash2.ind

section
variable {α : Type _}
ifix clash3 [OFE α] (x x' : α) : PROP := iprop% ▷ clash3 x' x
#check @clash3.ne
end

/-! ## Universe polymorphism and many varying parameters -/

universe u
ifix allL {A : Type u} (P : A → PROP) (l : List A) : PROP :=
  match l with
  | [] => iprop(True)
  | x :: xs => iprop(P x ∗ allL P xs)
#check @allL.iter

ifix four (a : Nat) (b : Int) (c : Bool) (d : List Nat) : PROP :=
  iprop(⌜a = 0⌝ ∨ four (a - 1) (b + 1) (!c) (a :: d))
#check @four.iter
#check @four.unfold
example : Persistent (four (PROP := PROP) 3 0 true []) := inferInstance

/-! ## Generated statements contain no internal projections -/

open Lean Meta Elab Command in
elab "#check_clean " ns:ident : command => do
  let env ← getEnv
  let bad := [``Iris.IOrder.le, ``Iris.IMeet.meet, ``Iris.INe.ne, ``Lean.Order.PartialOrder.rel,
    ``Iris.PointwiseLifting.rel, ``Iris.PointwiseLifting.map, ``Iris.PointwiseLifting.zip,
    ``Iris.PointwiseLifting.all, ``Iris.IPointwiseLifting.irel, ``Iris.IOrder.IMono,
    ``Lean.Order.fix]
  for sfx in [`pre_mono, `unfold, `iter, `coiter, `ind, `coind, `ind_wf, `paco, `strong_mono, `ne,
      `affine, `absorbing, `persistent_affine, `persistent_absorbing] do
    let n := (← getCurrNamespace) ++ ns.getId ++ sfx
    if let some ci := env.find? n then
      for c in bad do
        if (ci.type.find? (·.isConstOf c)).isSome then logError m!"{n} mentions {c}"
      if (ci.type.find? (·.isMData)).isSome then logError m!"{n} has mdata"

#check_clean even
#check_clean eo
#check_clean eo2
#check_clean lseg
#check_clean lseg2
#check_clean stream
#check_clean forever
#check_clean spin
#check_clean vec
#check_clean finP
#check_clean walk
#check_clean reach
#check_clean pa
#check_clean clash
#check_clean clash2
#check_clean clash3
#check_clean allL
#check_clean four


/-! ## Monotonicity in a fixed parameter, via `strong_mono` -/

theorem stream_mono (P Q : Nat → PROP) (h : ∀ n, Q n ⊢ P n) (n : Nat) : stream Q n ⊢ stream P n := by
  iintro H
  iapply (stream.strong_mono P (stream.pre Q) (stream Q) (fun k => by rw [stream.unfold])) $$ [] H
  iintro !> %Φ %k ⟨HQ, HΦ⟩
  isplitl [HQ]
  · iapply h; iexact HQ
  · iexact HΦ

theorem lseg_mono (pt pt' : Nat → Nat → Nat → PROP) (h : ∀ a b c, pt a b c ⊢ pt' a b c)
    (p q : Nat) (l : List Nat) : lseg pt p q l ⊢ lseg pt' p q l := by
  iintro H
  iapply (lseg.strong_mono pt q (lseg.pre pt' q) (fun p l => lseg pt' p q l)
    (fun p l => by rw [lseg.unfold])) $$ [] H
  iintro !> %Φ %p %l H
  cases l with
  | nil => iexact H
  | cons x xs =>
    simp only [lseg.pre]
    icases H with ⟨%p', Hpt, H⟩
    iexists p'
    isplitl [Hpt]
    · iapply h; iexact Hpt
    · iexact H

/-! ## Implicit varying parameter in a motive -/

theorem vec_len {n : Nat} (v : Fin n → Nat) : vec (PROP := PROP) v ⊢ True := by
  iintro H
  iapply (vec.iter (PROP := PROP) (fun _ _ => iprop(True))) $$ [] H
  iintro !> %n %v _
  ipureintro; trivial

/-! ## `paco` with an accumulator distinct from the goal -/

icofix ones (n : Nat) : PROP := iprop% ⌜n = 1⌝ ∗ ▷ ones n
-- `n` is passed unchanged, so it is inferred fixed: no varying parameter.
#check @ones.paco

icofix cnt (n : Nat) : PROP := iprop% ⌜0 < n⌝ ∗ ▷ cnt (n + 1)

theorem cnt_intro : ⊢@{PROP} cnt 1 := by
  iapply (cnt.paco (fun n => iprop(⌜0 < n⌝)) (fun n => iprop(⌜0 < n⌝))
    (fun n => by iintro %h; ileft; ipureintro; exact h)) $$ []
  · iintro !> %n %h
    isplitr
    · ipureintro; exact h
    · inext; ipureintro; omega
  · ipureintro; omega

/-! ## `iguarded` laws in use -/

section
variable [BILaterContractive PROP] [Inhabited PROP]

iguarded gstream (P : Nat → PROP) (n : Nat) : PROP := iprop% P n ∗ ▷ gstream P (n + 1)
contractive_by
  intros k Φ Ψ h P n; unfold gstream.pre
  exact sep_ne.ne .rfl (Contractive.distLater_dist fun m hm => h m hm _ _)

#check @gstream.unfold
#check @gstream.persistent
#check @gstream.absorbing

theorem gstream_head (P : Nat → PROP) (n : Nat) : gstream P n ⊢ P n ∗ ▷ gstream P (n + 1) := by
  rw [gstream.unfold]

-- Known: `iguarded` treats every parameter as varying, so the law quantifies over every `P`, and
-- persistence of `gstream P` for a persistent `P` is out of reach.
/--
error: failed to synthesize instance of type class
  Persistent iprop(P n ∗ ▷ x✝ P (n + 1))

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example (P : Nat → PROP) [∀ n, Persistent (P n)] (n : Nat) : Persistent (gstream P n) :=
  gstream.persistent (fun _ h P n => by unfold gstream.pre; have := h P (n + 1); infer_instance) P n

-- The Banach laws are not instances.
/--
error: failed to synthesize instance of type class
  Persistent (gstream P n)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example (P : Nat → PROP) [∀ n, Persistent (P n)] (n : Nat) : Persistent (gstream P n) :=
  inferInstance
end

/-! ## Nesting: one fixpoint inside another -/

ifix outer (n : Nat) : PROP := iprop% even n ∗ (⌜n = 0⌝ ∨ outer (n - 2))
example (n : Nat) : Persistent (outer (PROP := PROP) n) := inferInstance

-- BUG(usability): a recursive call under another `icofix`'s fixed predicate parameter is
-- rejected: no `@[imono]` rule is emitted for monotonicity in fixed parameters (although
-- `strong_mono` proves it). No laws are emitted after the error.
/--
error: imono: no rule for IrisTest.Stress.LawsInUse.stream, after unfolding it once
-/
#guard_msgs in
ifix nest (n : Nat) : PROP := iprop% ⌜n = 0⌝ ∨ ▷ stream (fun m => nest (m - n)) 0

/-! ## Instance-implicit fixed parameters -/

ifix boxed (P : PROP) [Persistent P] (n : Nat) : PROP := iprop% P ∗ (⌜n = 0⌝ ∨ boxed P (n - 1))
#check @boxed.iter
#check @boxed.persistent_absorbing
example (P : PROP) [Persistent P] (n : Nat) : Persistent (boxed P n) := inferInstance

theorem boxed_P (P : PROP) [Persistent P] (n : Nat) : boxed P n ⊢ <pers> P := by
  iintro H
  iapply (boxed.iter P (fun _ => iprop(<pers> P))) $$ [] H
  iintro !> %k ⟨#HP, _⟩
  imodintro; iexact HP

/-! ## `name.pre` is exposed and compiled -/

-- the generated instances work in exported definitions
theorem evenAbs (n : Nat) : Absorbing (even (PROP := PROP) n) := inferInstance

-- `name.pre` is compiled
abbrev evenPre (Φ : Nat → PROP) (n : Nat) : PROP := even.pre Φ n

open Lean in
/-- info: true -/
#guard_msgs in
#eval show Elab.Command.CommandElabM Bool from do
  return ((← getEnv).setExporting true).find? ``even.pre |>.any (·.hasValue)

end IrisTest.Stress.LawsInUse
