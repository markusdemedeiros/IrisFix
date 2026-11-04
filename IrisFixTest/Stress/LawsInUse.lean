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
  iapply (lseg.iter (fun pt' p q' xs => iprop(∀ (_ : pt' = pt) (_ : q' = q),
    lseg pt q r ys -∗ lseg pt p r (xs ++ ys)))) $$ [] %pt %p %q %xs H1 %rfl %rfl
  iintro !> %pt' %p %q' %xs Hxs %hpt %hq H2
  subst hpt hq
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
    iapply Hih $$ %rfl %rfl H2

-- a parameter passed on unchanged in the middle, after a changing one
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
  iapply (lseg2.iter (fun p _ l q => iprop(⌜l = [] → p = q⌝))) $$ [] %p %pt %l %q H
  iintro !> %p %pt %l %q Hl
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
  lseg.absorbing (h := fun pt p q l => by cases l <;> simp only [lseg.pre] <;> infer_instance) pt p q l
-- The persistence law needs persistent cells at every `pt`: with `pt` fixed (a section variable).
section
variable (pt : Nat → Nat → Nat → PROP) [∀ a b c, Persistent (pt a b c)]
ifix lsegS (p q : Nat) (l : List Nat) : PROP :=
  match l with
  | [] => iprop(⌜p = q⌝)
  | x :: xs => iprop(∃ p', pt p x p' ∗ lsegS p' q xs)
example (p q : Nat) (l : List Nat) : Persistent (lsegS pt p q l) :=
  have : ∀ p q l, Absorbing (lsegS pt p q l) :=
    lsegS.absorbing pt (h := fun p q l => by cases l <;> simp only [lsegS.pre] <;> infer_instance)
  lsegS.persistent_absorbing pt
    (hP := fun p q l => by cases l <;> simp only [lsegS.pre] <;> infer_instance) p q l
end


/-! ## Coinductive streams -/

icofix stream (P : Nat → PROP) (n : Nat) : PROP := iprop% P n ∗ ▷ stream P (n + 1)

#check @stream.coiter
#check @stream.paco

-- `rw [name.pre]` and the equation lemmas `name.pre.eq_1` / `name.pre.eq_def` work.
example (P : Nat → PROP) (Φ : (Nat → PROP) → Nat → PROP) (n : Nat) :
    stream.pre Φ P n = iprop(P n ∗ ▷ Φ P (n + 1)) := by
  rw [stream.pre]

example (Φ : Nat → PROP) (n : Nat) :
    even.pre Φ n = iprop(⌜n = 0⌝ ∨ ∃ m, ⌜n = m + 2⌝ ∗ Φ m) := even.pre.eq_def Φ n
example (Φ : Nat → PROP) (n : Nat) :
    even.pre Φ n = iprop(⌜n = 0⌝ ∨ ∃ m, ⌜n = m + 2⌝ ∗ Φ m) := even.pre.eq_1 Φ n

-- `unfold`, `simp only`, `dsimp only`, `delta` and `rfl` do work.
example (P : Nat → PROP) (Φ : (Nat → PROP) → Nat → PROP) (n : Nat) :
    stream.pre Φ P n = iprop(P n ∗ ▷ Φ P (n + 1)) := by
  unfold stream.pre; rfl
example (P : Nat → PROP) (Φ : (Nat → PROP) → Nat → PROP) (n : Nat) :
    stream.pre Φ P n = iprop(P n ∗ ▷ Φ P (n + 1)) := by
  simp only [stream.pre]
example (P : Nat → PROP) (Φ : (Nat → PROP) → Nat → PROP) (n : Nat) :
    stream.pre Φ P n = iprop(P n ∗ ▷ Φ P (n + 1)) := rfl

theorem stream_of_all' (P : Nat → PROP) [∀ n, Persistent (P n)] (n : Nat) :
    (□ ∀ k, P k) ⊢ stream P n := by
  iintro #HP
  iapply (stream.coiter (fun Q _ => iprop(∃ _ : Q = P, □ ∀ k, P k))) $$ [] %P %n [HP]
  · iintro !> %Q %k ⟨%hQ, #H⟩
    subst hQ
    isplitl
    · iapply H
    · inext; iexists rfl; iexact H
  · iexists rfl; iexact HP

-- coind: use the coinductive hypothesis disjunct
theorem stream_coind_use (P : Nat → PROP) [∀ n, Persistent (P n)] (n : Nat) :
    (□ ∀ k, P k) ⊢ stream P n := by
  iintro #HP
  iapply (stream.coind (fun Q _ => iprop(∃ _ : Q = P, □ ∀ k, P k))) $$ [] %P %n [HP]
  · iintro !> %Q %k ⟨%hQ, #H⟩
    subst hQ
    isplitl
    · iapply H
    · inext; ileft; iexists rfl; iexact H
  · iexists rfl; iexact HP

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
  iapply (stream.paco stream stream
    (fun P k => by iintro H; iright; rw [stream.unfold]; iexact H)) $$ [] %P %n H
  iintro !> %Q %k H
  rw [stream.unfold]; iexact H

-- absorbing instance
example (P : Nat → PROP) [∀ n, Absorbing (P n)] (n : Nat) : Absorbing (stream P n) := inferInstance
example (P : Nat → PROP) [∀ n, Absorbing (P n)] (n : Nat) : stream P n ∗ P 0 ⊢ stream P n := by
  iintro ⟨H, -⟩; iexact H

-- pre_mono for a gfp
example (P : Nat → PROP) (Φ Ψ : (Nat → PROP) → Nat → PROP) (h : ∀ P n, Φ P n ⊢ Ψ P n) (n : Nat) :
    stream.pre Φ P n ⊢ stream.pre Ψ P n := by
  iintro H
  iapply (stream.pre_mono Ψ Φ) $$ [] %P %n H
  iintro !> %Q %k Hk; iapply h; iexact Hk

-- strong_mono for a gfp
#check @stream.strong_mono

/-! ## A parameter passed on unchanged, and no parameter -/

icofix forever (P : PROP) : PROP := iprop% P ∗ ▷ forever P
#check @forever.unfold
#check @forever.coiter
#check @forever.coind
#check @forever.paco
#check @forever.absorbing
theorem forever_intro (P : PROP) [Persistent P] : □ P ⊢ forever P := by
  iintro #H
  iapply (forever.coiter (fun Q => iprop(∃ _ : Q = P, □ P))) $$ [] %P [H]
  · iintro !> %Q ⟨%hQ, #H⟩
    subst hQ
    isplitl
    · iexact H
    · inext; iexists rfl; iexact H
  · iexists rfl; iexact H

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

-- A law takes the section variables that it uses, like a theorem: `ne` takes `[OFE α]`.
ifix walkS (x : α) (k : Nat) (y : α) : PROP := iprop% ▷ walkS y k x
#check @walkS.ne
end

section
variable {α : Type _}

ifix walk [OFE α] (x : α) (k : Nat) (y : α) : PROP := iprop% ▷ walk y k x
#check @walk.ne

example [OFE α] {n : Nat} (k : Nat) {x x' y y' : α} (hx : x ≡{n}≡ x') (hy : y ≡{n}≡ y') :
    walk (PROP := PROP) x k y ≡{n}≡ walk x' k y' :=
  walk.ne (fun _ _ hf x x' hx k y y' hy => later_ne.ne (hf y y' hy k x x' hx)) x x' hx k y y' hy

-- `NonExpansive` from `ne`
example [OFE α] (k : Nat) (y : α) : NonExpansive (fun x => walk (PROP := PROP) x k y) :=
  ⟨fun {_} x x' hx => walk.ne (fun _ _ hf x x' hx k y y' hy => later_ne.ne (hf y y' hy k x x' hx))
    x x' hx k y y .rfl⟩
end

section
-- a fixed OFE argument (a section variable), changing Nat
variable (x : PROP)
ifix chainP (k : Nat) : PROP := iprop% x ∗ (⌜k = 0⌝ ∨ ▷ chainP (k - 1))
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
  iapply (reach.iter (fun R' a b' => iprop(∀ (_ : R' = R) (_ : b' = b),
    reach R b c -∗ reach R a c))) $$ [] %R %a %b H1 %rfl %rfl
  iintro !> %R' %a %b' Hab %hR %hb H2
  subst R' b'
  icases Hab with (%h | ⟨%d, %hd, Hih⟩)
  · subst h; iexact H2
  · rw [reach.unfold R a c]; iright; iexists d; isplitr
    · ipureintro; exact hd
    · iapply Hih $$ %rfl %rfl H2

-- iter with every parameter generalized.
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
-- With `P` fixed (a section variable), the instance needs `Persistent P`.
section
variable (P : PROP) [Persistent P]
ifix npS (n : Nat) : PROP := iprop% P ∗ npS n
example (n : Nat) : Persistent (npS P n) := inferInstance
end

-- A body that uses no BI operation still gets the `[BI PROP]` section variable (`local bi`).
ifix selfloop (n : Nat) : PROP := iprop% selfloop n
example (n : Nat) : Persistent (selfloop (PROP := PROP) n) := inferInstance
example (n : Nat) : selfloop (PROP := PROP) n = selfloop.pre selfloop n := selfloop.unfold n

-- With the instance in the binders.
ifix selfloop' [BI PROP] (n : Nat) : PROP := iprop% selfloop' n
example (n : Nat) : Persistent (selfloop' (PROP := PROP) n) := inferInstance
example (n : Nat) : Affine (selfloop' (PROP := PROP) n) := inferInstance

/-! ## Binder names that clash with the law's own names -/

ifix clash (Φ : PROP) (W : Nat) : PROP := iprop% Φ ∗ clash Φ (W + 1)
#check @clash.iter
#check @clash.ind_wf
-- the motive is primed: `Φ'`
#check clash.iter (PROP := PROP) (Φ' := fun _ _ => iprop(True))

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

/-! ## Generated statements contain no internal projections -/

open Lean Meta Elab Command in
elab "#check_clean " ns:ident : command => do
  let env ← getEnv
  let bad := [``Iris.IOrder.le, ``Iris.IOrder.meet, ``Iris.INe.ne, ``Lean.Order.PartialOrder.rel,
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


/-! ## Monotonicity in a parameter passed on unchanged, via `strong_mono` -/

theorem stream_mono (P Q : Nat → PROP) (h : ∀ n, Q n ⊢ P n) (n : Nat) : stream Q n ⊢ stream P n := by
  iintro H
  iapply (stream.strong_mono (fun Φ R k => iprop(∃ _ : R = P, Q k ∗ ▷ Φ R (k + 1)))
    (fun R k => iprop(∃ _ : R = P, stream Q k))
    (fun R k => by
      iintro ⟨%hR, H⟩; rw [stream.unfold]; icases H with ⟨HQ, H⟩
      iexists hR; iframe; iexists hR; iexact H)) $$ [] %P %n [H]
  · iintro !> %Φ %R %k ⟨%hR, HQ, HΦ⟩
    subst hR
    isplitl [HQ]
    · iapply h; iexact HQ
    · iexact HΦ
  · iexists rfl; iexact H

theorem lseg_mono (pt pt' : Nat → Nat → Nat → PROP) (h : ∀ a b c, pt a b c ⊢ pt' a b c)
    (p q : Nat) (l : List Nat) : lseg pt p q l ⊢ lseg pt' p q l := by
  iintro H
  iapply (lseg.strong_mono
    (fun Φ pt₀ p q l => iprop(∀ _ : pt₀ = pt, lseg.pre (fun _ => Φ pt) pt' p q l))
    (fun pt₀ p q l => iprop(∀ _ : pt₀ = pt, lseg pt' p q l))
    (fun pt₀ p q l => by
      iintro H %hpt; ispecialize H $$ %hpt; rw [lseg.unfold]
      cases l with
      | nil => iexact H
      | cons x xs => icases H with ⟨%p', Hpt, H⟩; iexists p'; iframe; iapply H $$ %rfl))
    $$ [] %pt %p %q %l H %rfl
  iintro !> %Φ %pt₀ %p %q %l H %hpt
  subst hpt
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
  iapply (vec.iter (PROP := PROP) (fun _ _ => iprop(True))) $$ [] %n %v H
  iintro !> %n %v _
  ipureintro; trivial

/-! ## `paco` with an accumulator distinct from the goal -/

icofix ones (n : Nat) : PROP := iprop% ⌜n = 1⌝ ∗ ▷ ones n
-- `n` is passed unchanged, and still a parameter of the motive.
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

-- Limitation: every parameter varies, and an instance of a `Prop` class is a proof, out of scope.
/--
error: failed to synthesize
  PointwiseLifting PROP ((P : PROP) → [Persistent P] → Nat → PROP)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
---
warning: unused `partial_fixpoint`, function is not recursive
-/
#guard_msgs in
ifix boxed (P : PROP) [Persistent P] (n : Nat) : PROP := iprop% P ∗ (⌜n = 0⌝ ∨ boxed P (n - 1))

-- Fixed, as section variables.
section
variable (P : PROP) [Persistent P]
ifix boxedS (n : Nat) : PROP := iprop% P ∗ (⌜n = 0⌝ ∨ boxedS (n - 1))
#check @boxedS.iter
#check @boxedS.persistent_absorbing
example (n : Nat) : Persistent (boxedS P n) := inferInstance

theorem boxed_P (n : Nat) : boxedS P n ⊢ <pers> P := by
  iintro H
  iapply (boxedS.iter P (fun _ => iprop(<pers> P))) $$ [] H
  iintro !> %k ⟨#HP, _⟩
  imodintro; iexact HP
end

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
