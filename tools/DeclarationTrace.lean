import Lean

open Lean

namespace DeclarationTrace

def dependencies (ci : ConstantInfo) : NameSet := Id.run do
  let mut refs := ci.type.getUsedConstantsAsSet
  if let some body := ci.value? (allowOpaque := true) then
    refs := refs.append body.getUsedConstantsAsSet
  match ci with
  | .inductInfo data =>
      for n in data.ctors ++ data.all do refs := refs.insert n
  | .ctorInfo data => refs := refs.insert data.induct
  | .recInfo data =>
      for rule in data.rules do
        refs := refs.insert rule.ctor
        refs := refs.append rule.rhs.getUsedConstantsAsSet
  | _ => pure ()
  return refs

partial def moduleOf? (env : Environment) (name : Name) : Option Name :=
  match env.getModuleIdxFor? name with
  | some idx => env.header.moduleNames[idx.toNat]?
  | none => if name.isAnonymous then none else moduleOf? env name.getPrefix

def isProjectModule (name : Name) : Bool := name.getRoot == `Wikipedia

def trace (roots : Array Name) : CoreM Unit := do
  let env ← getEnv
  let mut stack := roots
  let mut seen : NameSet := {}
  let mut opaqueMissing : Array Name := #[]
  while !stack.isEmpty do
    let name := stack.back!
    stack := stack.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some ci := env.find? name
      | throwError "Missing dependency {name}"
    if ci matches .thmInfo _ then
      if (ci.value? (allowOpaque := true)).isNone then
        opaqueMissing := opaqueMissing.push name
    for dep in dependencies ci do
      if !seen.contains dep then stack := stack.push dep
  if !opaqueMissing.isEmpty then
    throwError "Theorem bodies unavailable: {opaqueMissing}"
  let mut liveMods : NameSet := {}
  let mut counts := (0, 0)
  for (name, _) in env.constants.toList do
    let some mod := moduleOf? env name | continue
    if !isProjectModule mod then continue
    let live := seen.contains name
    counts := (counts.1 + 1, counts.2 + if live then 1 else 0)
    if live then liveMods := liveMods.insert mod
    let tag := if live then "LIVE" else "DEAD"
    match ← findDeclarationRanges? name with
    | some r =>
        IO.println s!"{tag}|{mod}|{name}|{r.range.pos.line}|{r.range.endPos.line}"
    | none => IO.println s!"{tag}|{mod}|{name}|?|?"
  for mod in env.header.moduleNames do
    if isProjectModule mod && !liveMods.contains mod then IO.println s!"DEADMOD|{mod}"
  IO.println s!"# project constants: {counts.1}; live: {counts.2}; total closure: {seen.size}"
  for name in seen.toList do
    if let some (.axiomInfo _) := env.find? name then IO.println s!"AXIOM|{name}"

end DeclarationTrace

def main (args : List String) : IO Unit := do
  unsafe Lean.enableInitializersExecution
  initSearchPath (← findSysroot)
  let mod := (args[0]?.getD "Wikipedia.NoExoticSixSphere.Classification").toName
  let root := (args[1]?.getD "NoExoticSixSphere.noExoticSixSpheres").toName
  let extraRoots := (args.drop 2).toArray.map String.toName
  let env ← importModules #[{ module := mod, importAll := true }] {}
    (loadExts := true) (level := .private)
  DeclarationTrace.trace (#[root] ++ extraRoots) |>.toIO'
    { fileName := "DeclarationTrace", fileMap := FileMap.ofString "" }
    { env := env }
