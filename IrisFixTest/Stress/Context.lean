module

public import Iris.BI
public import Iris.Instances.UPred.Instance
public import IrisFix.ProofMode.Lib.Fixpoint
public import IrisFix.ProofMode.Lib.Guarded

/-! Stress tests: the elaboration context of `ifix` / `icofix` / `iguarded`. -/

@[expose] public section
open Iris BI OFE

/-! ## Inside the scoped-instance namespaces themselves -/

namespace Iris.MonotoneFixpoint
variable {PROP : Type _} [BI PROP]
-- The macro's own `open scoped` wins over the ambient scoped instances.
icofix ctxInMono (n : Nat) : PROP := iprop% ▷ ctxInMono (n + 1)
example (Φ : Nat → PROP) :
    ⊢ □ (∀ n, Φ n -∗ ctxInMono.pre Φ n) -∗ ∀ n, Φ n -∗ ctxInMono n :=
  ctxInMono.coiter Φ
end Iris.MonotoneFixpoint

namespace Iris.CoMonotoneFixpoint
variable {PROP : Type _} [BI PROP]
ifix ctxInCo (n : Nat) : PROP := iprop% ⌜n = 0⌝ ∨ ctxInCo (n + 1)
example (Φ : Nat → PROP) : ⊢ □ (∀ n, ctxInCo.pre Φ n -∗ Φ n) -∗ ∀ n, ctxInCo n -∗ Φ n :=
  ctxInCo.iter Φ
end Iris.CoMonotoneFixpoint

/-! ## Top level, with an opened namespace that has a clashing `.pre` name -/

namespace IrisTest.Stress.ContextOther
def gtop.pre : Nat := 0
end IrisTest.Stress.ContextOther

section
open IrisTest.Stress.ContextOther
variable {PROP : Type _} [BI PROP] [BILaterContractive PROP] [Inhabited PROP]
iguarded ctxTop (n : Nat) : PROP := iprop% ▷ ctxTop (n + 1)
contractive_by
  intros k Φ Ψ h n; unfold _root_.ctxTop.pre
  exact Contractive.distLater_dist (fun m hm => h m hm _)
example (n : Nat) : ctxTop (PROP := PROP) n = ctxTop.pre ctxTop n := ctxTop.unfold n
end

namespace IrisTest.Stress.Context

local bi PROP

variable {PROP : Type _} [BI PROP]

/-! ## Namespaces, dotted names -/

namespace A.B
ifix ev (n : Nat) : PROP := iprop% ⌜n = 0⌝ ∨ ∃ m, ⌜n = m + 2⌝ ∗ ev m
example (n : Nat) : ev (PROP := PROP) n = ev.pre ev n := ev.unfold n
end A.B

example (Φ : Nat → PROP) : ⊢ □ (∀ n, A.B.ev.pre Φ n -∗ Φ n) -∗ ∀ n, A.B.ev n -∗ Φ n :=
  A.B.ev.iter Φ

section
open A.B
example (n : Nat) : Persistent (ev (PROP := PROP) n) := inferInstance
example (n : Nat) : ev (PROP := PROP) n = ev.pre ev n := ev.unfold n
end

ifix Foo.bar (n : Nat) : PROP := iprop% ⌜n = 0⌝ ∨ Foo.bar (n + 1)
example (n : Nat) : Foo.bar (PROP := PROP) n = Foo.bar.pre Foo.bar n := Foo.bar.unfold n

/-! ## `_root_` -/

ifix _root_.ctxRootFix (n : Nat) : PROP := iprop% ⌜n = 0⌝ ∨ ctxRootFix (n + 1)
example (n : Nat) : ctxRootFix (PROP := PROP) n = ctxRootFix.pre ctxRootFix n := ctxRootFix.unfold n
example (Φ : Nat → PROP) : ⊢ □ (∀ n, ctxRootFix.pre Φ n -∗ Φ n) -∗ ∀ n, ctxRootFix n -∗ Φ n :=
  ctxRootFix.iter Φ

/-! ## Visibility and modifiers -/

private ifix pf (n : Nat) : PROP := iprop% ⌜n = 0⌝ ∨ pf (n + 1)
example (n : Nat) : pf (PROP := PROP) n = pf.pre pf n := pf.unfold n

protected ifix Prot.pf (n : Nat) : PROP := iprop% ⌜n = 0⌝ ∨ Prot.pf (n + 1)
example (n : Nat) : Prot.pf (PROP := PROP) n = Prot.pf.pre Prot.pf n := Prot.pf.unfold n

noncomputable ifix ncFix (n : Nat) : PROP := iprop% ⌜n = 0⌝ ∨ ncFix (n + 1)

noncomputable section
ifix ncs (n : Nat) : PROP := iprop% ⌜n = 0⌝ ∨ ncs (n + 1)
end

/-- docstring on the definition -/
ifix docFix (n : Nat) : PROP := iprop% ⌜n = 0⌝ ∨ docFix (n + 1)

@[reducible] ifix rd (n : Nat) : PROP := iprop% ⌜n = 0⌝ ∨ rd (n + 1)
@[local simp] ifix ls (n : Nat) : PROP := iprop% ⌜n = 0⌝ ∨ ls (n + 1)

set_option pp.all false in
ifix so (n : Nat) : PROP := iprop% ⌜n = 0⌝ ∨ so (n + 1)

/-! ## Defining a name twice, clashes -/

ifix twice (n : Nat) : PROP := iprop% ⌜n = 0⌝ ∨ twice (n + 1)

-- Rejected: `twice` is already defined.
/-- error: `IrisTest.Stress.Context.twice` has already been declared -/
#guard_msgs in
ifix twice (n : Nat) : PROP := iprop% ⌜n = 0⌝ ∨ twice (n + 1)

def clash : Nat := 0
-- Rejected: `clash` is already defined (by an unrelated `def`).
/-- error: `IrisTest.Stress.Context.clash` has already been declared -/
#guard_msgs in
ifix clash (n : Nat) : PROP := iprop% ⌜n = 0⌝ ∨ clash (n + 1)

def nc.pre : Nat := 0
-- Rejected: a generated name (`nc.pre`, `nc2.iter`) already exists.
/-- error: cannot generate `IrisTest.Stress.Context.nc.pre`: a declaration with this name already exists -/
#guard_msgs in
ifix nc (n : Nat) : PROP := iprop% ⌜n = 0⌝ ∨ nc (n + 1)

def nc2.iter : Nat := 0
/--
error: cannot generate `IrisTest.Stress.Context.nc2.iter`: a declaration with this name already exists
-/
#guard_msgs in
ifix nc2 (n : Nat) : PROP := iprop% ⌜n = 0⌝ ∨ nc2 (n + 1)
-- The clash is detected before anything is defined: `nc2` itself does not exist.
/-- error: Unknown identifier `nc2` -/
#guard_msgs in
#check nc2

/-! ## Universes -/

universe u v

ifix uni4 {R : Type (u + 1)} [BI R] (n : Nat) : R := iprop% ⌜n = 0⌝ ∨ uni4 (n + 1)
example {R : Type (u + 1)} [BI R] (n : Nat) : uni4 (R := R) n = uni4.pre uni4 n := uni4.unfold n

ifix uni2.{w} {R : Type w} [BI R] (n : Nat) : R := iprop% ⌜n = 0⌝ ∨ uni2 (n + 1)
example {R : Type v} [BI R] (n : Nat) : uni2 (R := R) n = uni2.pre (R := R) uni2 n := uni2.unfold n

section
variable {Q : Type u} [BI Q]
ifix uniSec (n : Nat) : Q := iprop% ⌜n = 0⌝ ∨ uniSec (n + 1)
example (n : Nat) : uniSec (Q := Q) n = uniSec.pre uniSec n := uniSec.unfold n
end

-- Universes only the body mentions.
ifix ub (n : Nat) : PROP := iprop% ⌜(ULift.{v} Nat) = (ULift.{v} Nat)⌝ ∨ ub (n + 1)
ifix ub2.{w} (n : Nat) : PROP := iprop% ⌜(ULift.{w} Nat) = (ULift.{w} Nat)⌝ ∨ ub2 (n + 1)
example (n : Nat) : ub2.{0} (PROP := PROP) n = ub2.pre.{0} ub2.{0} n := ub2.unfold n

-- Rejected: `w` is declared but unused.
/-- error: unused universe parameter 'w' -/
#guard_msgs in
ifix uniUnused.{w} (n : Nat) : PROP := iprop% ⌜n = 0⌝ ∨ uniUnused (n + 1)

/-! ## Section variables -/

section
variable (P : PROP) (Q : PROP) [BIAffine PROP]
ifix withP (n : Nat) : PROP := iprop% P ∗ withP (n + 1)
-- `Q` and `[BIAffine PROP]` are unused, so omitted; `P` is a fixed parameter.
example (n : Nat) : withP P n = withP.pre P (withP P) n := withP.unfold P n
example (Φ : Nat → PROP) : ⊢ □ (∀ n, withP.pre P Φ n -∗ Φ n) -∗ ∀ n, withP P n -∗ Φ n :=
  withP.iter P Φ
example (n : Nat) : Affine (withP P n) := inferInstance
end

example [BIAffine PROP] (P : PROP) (n : Nat) : Affine (withP P n) := inferInstance

section
variable (A : Type) [inst : Inhabited A] (a0 : A)
ifix tA (x : A) (n : Nat) : PROP := iprop% ⌜x = a0⌝ ∨ tA x (n + 1)
example (x : A) (n : Nat) : tA (PROP := PROP) A a0 x n = tA.pre A a0 x (tA A a0 x) n := tA.unfold A a0 x n
-- A section instance used only by the body; `x` varies here.
ifix tB (x : A) (n : Nat) : PROP := iprop% ⌜x = default⌝ ∨ tB a0 (n + 1)
example (Φ : A → Nat → PROP) :
    ⊢ □ (∀ x n, tB.pre A a0 Φ x n -∗ Φ x n) -∗ ∀ x n, tB A a0 x n -∗ Φ x n :=
  tB.iter A a0 Φ
end

set_option autoImplicit true in
ifix aimp [OFE α] (x y : α) : PROP := iprop% ▷ aimp y x
example {α : Type} [OFE α] (x y : α) : aimp (PROP := PROP) x y = aimp.pre aimp x y :=
  aimp.unfold x y

/-! ## Several BIs, concrete BIs -/

section
variable {P2 : Type _} [BI P2]
ifix twoBI (f : P2 → PROP) (p : P2) (n : Nat) : PROP := iprop% f p ∨ twoBI f p (n + 1)
example (f : P2 → PROP) (p : P2) (n : Nat) : twoBI f p n = twoBI.pre f p (twoBI f p) n :=
  twoBI.unfold f p n
icofix twoBI2 (f : PROP → P2) (p : PROP) (n : Nat) : P2 := iprop% f p ∗ ▷ twoBI2 f p (n + 1)
-- (`local bi PROP` would put a `⊢` here at `PROP`, so no statement.)
example (f : PROP → P2) (p : PROP) (Φ : Nat → P2) := twoBI2.coiter f p Φ
end

section
variable {M : Type} [UCMRA M]
ifix uev (n : Nat) : UPred M := iprop% ⌜n = 0⌝ ∨ ∃ m, ⌜n = m + 2⌝ ∗ uev m
example (n : Nat) : Affine (uev (M := M) n) := inferInstance
example (n : Nat) : Persistent (uev (M := M) n) := inferInstance
icofix uco (n : Nat) : UPred M := iprop% ▷ uco (n + 1)
example (n : Nat) : Absorbing (uco (M := M) n) := inferInstance
local instance : Inhabited (UPred M) := ⟨iprop(True)⟩
iguarded ug (n : Nat) : UPred M := iprop% ▷ ug (n + 1)
contractive_by
  intros k Φ Ψ h n; unfold ug.pre; exact Contractive.distLater_dist (fun m hm => h m hm _)
example (n : Nat) : ug (M := M) n = ug.pre ug n := ug.unfold n
end

/-! ## Consecutive definitions -/

ifix ev (n : Nat) : PROP := iprop% ⌜n = 0⌝ ∨ ∃ m, ⌜n = m + 2⌝ ∗ ev m
ifix evOdd (n : Nat) : PROP := iprop% ev n ∨ ∃ m, ⌜n = m + 1⌝ ∗ evOdd m
example (Φ : Nat → PROP) : ⊢ □ (∀ n, evOdd.pre Φ n -∗ Φ n) -∗ ∀ n, evOdd n -∗ Φ n :=
  evOdd.iter Φ

-- Limitation: `ifix` is not accepted in a `mutual` block.
/--
error: invalid mutual block: either all elements of the block must be inductive/structure declarations, or they must all be definitions/theorems/abbrevs
-/
#guard_msgs in
mutual
ifix mA (n : Nat) : PROP := iprop% ⌜n = 0⌝ ∨ mB n
ifix mB (n : Nat) : PROP := iprop% mA (n + 1)
end

/-! ## `open` interactions; scoped instances do not leak -/

section
open Iris.MonotoneFixpoint
icofix coOpen (n : Nat) : PROP := iprop% ▷ coOpen (n + 1)
example (Φ : Nat → PROP) : ⊢ □ (∀ n, Φ n -∗ coOpen.pre Φ n) -∗ ∀ n, Φ n -∗ coOpen n :=
  coOpen.coiter Φ
end

section
open Iris.CoMonotoneFixpoint
ifix lfOpen (n : Nat) : PROP := iprop% ⌜n = 0⌝ ∨ lfOpen (n + 1)
example (Φ : Nat → PROP) : ⊢ □ (∀ n, lfOpen.pre Φ n -∗ Φ n) -∗ ∀ n, lfOpen n -∗ Φ n :=
  lfOpen.iter Φ
end

-- Not a bug: no order instance on `PROP` after the commands.
/--
error: failed to synthesize
  Lean.Order.CCPO PROP

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth Lean.Order.CCPO PROP

section
attribute [local instance high] Iris.MonotoneFixpoint.instCCPOMonoProp
-- Rejected: a stronger local `CCPO` instance of the other order overrides the one `icofix` needs.
/--
error: ifix_monotone: the order of
  Nat → PROP
is not the order of `IOrder`
-/
#guard_msgs in
icofix coHi (n : Nat) : PROP := iprop% ▷ coHi (n + 1)
end

-- No generated statement mentions the order classes or the scoped instances (except Lean's own
-- `fixpoint_induct`).
open Lean in
/-- info: [] -/
#guard_msgs in
#eval show Lean.Elab.Command.CommandElabM Unit from do
  let env ← getEnv
  let mut bad : Array Name := #[]
  for (n, ci) in env.constants.map₂.toList do
    unless (`IrisTest.Stress.Context).isPrefixOf n do continue
    if n.isInternal || n.getString! == "fixpoint_induct" then continue
    if ci.type.getUsedConstants.any fun c =>
      [`Iris.MonotoneFixpoint, `Iris.CoMonotoneFixpoint, `Lean.Order, `Iris.IOrder,
        `Iris.INe, `Iris.PointwiseLifting, `Iris.IPointwiseLifting].any
        (·.isPrefixOf c) then bad := bad.push n
  logInfo m!"{bad}"

/-! ## `iguarded` -/

section
variable [BILaterContractive PROP] [Inhabited PROP]

namespace N1.N2
iguarded g (n : Nat) : PROP := iprop% ▷ g (n + 1)
contractive_by
  intros k Φ Ψ h n; unfold g.pre; exact Contractive.distLater_dist (fun m hm => h m hm _)
example (n : Nat) : g (PROP := PROP) n = g.pre g n := g.unfold n
end N1.N2
example : N1.N2.g (PROP := PROP) = fixpoint N1.N2.g.pre := N1.N2.g.eq_fixpoint

example : Contractive (N1.N2.g.pre (PROP := PROP)) := N1.N2.g.pre.contractive
example : Contractive (N1.N2.g.pre (PROP := PROP)) := inferInstance

open Lean in
/-- info: true -/
#guard_msgs in
#eval show Lean.Elab.Command.CommandElabM Unit from do
  logInfo m!"{getReducibilityStatusCore (← getEnv) ``N1.N2.g == .irreducible}"

iguarded D.g (n : Nat) : PROP := iprop% ▷ D.g (n + 1)
contractive_by
  intros k Φ Ψ h n; unfold D.g.pre; exact Contractive.distLater_dist (fun m hm => h m hm _)
example (n : Nat) : D.g (PROP := PROP) n = D.g.pre D.g n := D.g.unfold n

iguarded _root_.ctxRg (n : Nat) : PROP := iprop% ▷ ctxRg (n + 1)
contractive_by
  intros k Φ Ψ h n; unfold ctxRg.pre; exact Contractive.distLater_dist (fun m hm => h m hm _)
example (n : Nat) : ctxRg (PROP := PROP) n = ctxRg.pre ctxRg n := ctxRg.unfold n

private iguarded pg (n : Nat) : PROP := iprop% ▷ pg (n + 1)
contractive_by
  intros k Φ Ψ h n; unfold pg.pre; exact Contractive.distLater_dist (fun m hm => h m hm _)
open Lean in
/-- info: true -/
#guard_msgs in
#eval show Lean.Elab.Command.CommandElabM Unit from do
  logInfo m!"{isPrivateName (← Lean.Elab.Command.liftCoreM (Lean.realizeGlobalConstNoOverload (mkIdent `pg)))}"

section
variable (P : PROP)
iguarded sg (n : Nat) : PROP := iprop% P ∗ ▷ sg (n + 1)
contractive_by
  intros k Φ Ψ h n; unfold sg.pre
  exact sep_ne.ne .rfl (Contractive.distLater_dist (fun m hm => h m hm _))
example (n : Nat) : sg P n = sg.pre P (sg P) n := sg.unfold P n
end

section
variable {k0 : Nat}
iguarded gi (n : Nat) : PROP := iprop% ⌜n = k0⌝ ∨ ▷ gi (n + 1)
contractive_by
  intros k Φ Ψ h n; unfold gi.pre
  exact or_ne.ne .rfl (Contractive.distLater_dist (fun m hm => h m hm _))
example (n : Nat) : gi (PROP := PROP) (k0 := k0) n =
    gi.pre (k0 := k0) (gi (k0 := k0)) n := gi.unfold n
end

iguarded gtw (n : Nat) : PROP := iprop% ▷ gtw (n + 1)
contractive_by
  intros k Φ Ψ h n; unfold gtw.pre; exact Contractive.distLater_dist (fun m hm => h m hm _)

-- Rejected: `gtw` is already defined.
/-- error: `IrisTest.Stress.Context.gtw` has already been declared -/
#guard_msgs in
iguarded gtw (n : Nat) : PROP := iprop% ▷ gtw (n + 1)
contractive_by
  intros k Φ Ψ h n; unfold gtw.pre; exact Contractive.distLater_dist (fun m hm => h m hm _)

end

end IrisTest.Stress.Context

/-! ## Use from another namespace, without `local bi` -/

namespace IrisTest.Stress.ContextUse
open Iris BI
variable {PROP : Type _} [BI PROP]
ifix noLocal (n : Nat) : PROP := iprop% ⌜n = 0⌝ ∨ noLocal (n + 1)
example (Φ : Nat → PROP) : ⊢ □ (∀ n, noLocal.pre Φ n -∗ Φ n) -∗ ∀ n, noLocal n -∗ Φ n :=
  noLocal.iter Φ
open IrisTest.Stress.Context in
example (n : Nat) : ev (PROP := PROP) n = ev.pre ev n := ev.unfold n
example (n : Nat) : Persistent (IrisTest.Stress.Context.ev (PROP := PROP) n) := inferInstance
end IrisTest.Stress.ContextUse
