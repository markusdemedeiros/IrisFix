/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public meta import Lean.Elab.Command
public meta import Lean.Elab.SyntheticMVars

/-! # Commands that generate declarations

Helpers for commands that elaborate a definition and then generate declarations about it: names,
elaboration that undoes itself on failure, reporting errors once, adding theorems, statements
whose binders avoid the names of parameters, and tactic proofs of generated goals. -/

public section

namespace Iris.Meta
open Lean Elab Command Term Meta

/-- The full name of the declaration `name` in the current namespace, as `def` names it. -/
meta def fullName (name : Name) : CommandElabM Name := do
  if name.getRoot == `_root_ then return name.replacePrefix `_root_ .anonymous
  return (← getCurrNamespace) ++ name

/-- The declaration `full`, just declared, perhaps private. -/
meta def resolveDeclared (full : Name) : CoreM Name := do
  let env ← getEnv
  if env.contains full then return full
  let priv := mkPrivateName env full
  if env.contains priv then return priv
  throwError "unknown declaration `{full}`"

/-- Fail if a declaration to be generated, `declName ++ s` for `s` in `suffixes`, exists. -/
meta def checkFresh (declName : Name) (suffixes : List Name) : CoreM Unit := do
  for s in suffixes do
    if (← getEnv).contains (declName ++ s) then
      throwError "cannot generate `{declName ++ s}`: a declaration with this name already exists"

/-- Elaborate the definition `cmd`. If it fails, undo it, report its errors once, and return
`false`. Errors inside the command replace the follow-ups at its start, about the definition as a
whole. -/
meta def elabDef (cmd : Syntax) : CommandElabM Bool := do
  let saved := (← get).messages
  let env ← getEnv
  modify ({ · with messages := {} })
  withScope (fun sc => { sc with opts := Elab.async.set sc.opts false }) <| elabCommand cmd
  let new := (← get).messages
  modify ({ · with messages := saved })
  unless new.hasErrors do
    modify ({ · with messages := saved ++ new })
    return true
  setEnv env
  let some start := (← getRef).getPos? | return false
  let start := (← getFileMap).toPosition start
  let inside (m : Message) := m.pos != start
  let msgs := new.toList
  let msgs := if msgs.any (fun m => m.severity == .error && inside m) then msgs.filter inside
    else msgs
  let mut seen : List String := []
  for m in msgs do
    let s ← m.toString
    unless seen.contains s do
      logMessage m
      seen := s :: seen
  return false

/-- Run `k` with a larger `synthInstance.maxSize`: the order of a function of many arguments is a
large instance. -/
meta def withLargeInstances {α} (k : CommandElabM α) : CommandElabM α :=
  withScope (fun sc => { sc with opts := synthInstance.maxSize.set sc.opts 4096 }) k

/-- `∀ bs, ty`, or `ty` without binders. -/
meta def forallStx {m} [Monad m] [MonadQuotation m] (bs : Array Syntax) (ty : Term) : m Term :=
  if bs.isEmpty then pure ty else `(∀ $(bs.map (⟨·⟩))*, $ty)

/-- `fun bs => e`, or `e` without binders. -/
meta def funStx {m} [Monad m] [MonadQuotation m] (bs : Array Syntax) (e : Term) : m Term :=
  if bs.isEmpty then pure e else `(fun $(bs.map (⟨·⟩))* => $e)

/-- The modifiers `mods`, and `noncomputable`, unless they say `meta`. -/
meta def addNoncomputableMod (mods : TSyntax ``Parser.Command.declModifiers) :
    CommandElabM (TSyntax ``Parser.Command.declModifiers) := do
  -- The fifth modifier is `meta` or `noncomputable`.
  if !mods.raw[4].isNone then return mods
  return ⟨mods.raw.setArg 4 (mkNullNode #[← `(Parser.Command.noncomputable| noncomputable)])⟩

/-- The modifiers `mods` of an auxiliary definition: without the doc comment and attributes. -/
meta def auxMods (mods : TSyntax ``Parser.Command.declModifiers) :
    TSyntax ``Parser.Command.declModifiers :=
  ⟨(mods.raw.setArg 0 mkNullNode).setArg 1 mkNullNode⟩

/-- Add a theorem; the kernel checks `value` against `type`. A theorem about a protected
declaration is protected. -/
meta def emitThm (name : Name) (levels : List Name) (type value : Expr) : MetaM Unit := do
  let type ← instantiateMVars type
  let value ← instantiateMVars value
  addDecl <| .thmDecl { name, levelParams := levels, type, value }
  if isProtected (← getEnv) name.getPrefix then modifyEnv (addProtected · name)

/-- Prime the binders of `e` that clash with `avoid`. -/
meta partial def primeNames (avoid : List Name) (e : Expr) : Expr :=
  e.replace fun
    | .forallE x t b bi => some (.forallE (prime x) (primeNames avoid t) (primeNames avoid b) bi)
    | _ => none
where prime x := if avoid.contains x then prime (x.appendAfter "'") else x

/-- The type of the law `value`, an application of a lemma, with the binders of the lemma that
clash with `avoid` (the parameters) primed. -/
meta def lawType (avoid : List Name) (value : Expr) : MetaM Expr := do
  let type := primeNames avoid (← inferType value.getAppFn)
  instantiateMVars (← instantiateForall type value.getAppArgs)

/-- The local variables of `e`, and of their types, transitively. -/
meta partial def fvarsOf (e : Expr) : MetaM (Std.HashSet FVarId) :=
  go (Lean.collectFVars {} e).fvarIds {}
where go (todo : Array FVarId) (acc : Std.HashSet FVarId) : MetaM (Std.HashSet FVarId) := do
  let some x := todo.back? | return acc
  if acc.contains x then return ← go todo.pop acc
  go (todo.pop ++ (Lean.collectFVars {} (← x.getType)).fvarIds) (acc.insert x)

/-- Elaborate the tactic proof `by tac` of `type`, or `mk (by tac)`, in the context of `type` alone
and the instances on it; `none` if it fails. -/
meta def proveBy (tac : Syntax) (type : Expr) (mk? : Option Name := none) :
    TermElabM (Option Expr) := do
  let mut keep ← fvarsOf type
  for d in (← getLCtx) do
    if d.binderInfo.isInstImplicit && (Lean.collectFVars {} d.type).fvarIds.all keep.contains then
      keep := keep.insert d.fvarId
  withErasedFVars ((← getLCtx).getFVarIds.filter (!keep.contains ·)) do
  let p ← elabTermEnsuringType (← match mk? with
    | some c => `($(mkCIdent c) (no_implicit_lambda% (by $(⟨tac⟩))))
    | none => `(by $(⟨tac⟩))) type
  synthesizeSyntheticMVarsNoPostponing
  let p ← instantiateMVars p
  return if p.hasSorry then none else some p

/-- Run `k` on the parameters `xs`, each one the section variable of `vars` of its name and type,
or else a new local. -/
meta partial def withSectionVars {α} (vars xs : Array Expr) (k : Array Expr → TermElabM α)
    (ys : Array Expr := #[]) : TermElabM α := do
  if h : ys.size < xs.size then
    let x := xs[ys.size]
    let d ← x.fvarId!.getDecl
    let ty := d.type.replaceFVars (xs.extract 0 ys.size) ys
    let v? ← vars.findM? fun v => do
      return (← v.fvarId!.getUserName).eraseMacroScopes == d.userName.eraseMacroScopes &&
        (← isDefEq (← inferType v) ty)
    match v? with
    | some v => withSectionVars vars xs k (ys.push v)
    | none =>
      withLocalDecl d.userName d.binderInfo ty fun y => withSectionVars vars xs k (ys.push y)
  else k ys

/-- Name the anonymous binders `_` of `bs`, so that they can be passed on. -/
meta def nameHoles (bs : Array Syntax) : CommandElabM (Array Syntax) :=
  bs.mapM fun b => do
    if b.getKind == ``Lean.Parser.Term.instBinder then return b
    let xs ← b[1].getArgs.mapM fun x => do
      if x.isOfKind ``Lean.Parser.Term.hole then return (← `(x)).raw else return x
    return b.setArg 1 (b[1].setArgs xs)

/-- `@f`, applied to its parameters by name, and to `_` for instances. -/
meta def applyByName (f : Name) : CommandElabM Term := liftTermElabM do
  forallTelescope (← getConstInfo f).type fun xs _ => do
    let args ← xs.mapM fun x => do
      let d ← x.fvarId!.getDecl
      if d.binderInfo.isInstImplicit then `(_) else return mkIdent d.userName
    `(@$(mkCIdent f) $args*)

end Iris.Meta
