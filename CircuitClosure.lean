import Lean
import Std.Data.HashMap
-- CircuitClosure.lean -- THE DEPENDENCY-CIRCUIT READING'S INPUT (relay data/b692_circuit_spec.txt :7-:12), under the author's ruling (R304)(3),
-- act b694, in (R302)(3)(a)'s form: SIDE-explicit-formula's CircuitClosure.lean at its 4313875 (act b692), the traversal unchanged. Imported by
-- no module of this kernel: the workflow's closure step writes out/Closure.lean -- an import of every module of the build's target, then this
-- file's text -- and runs it by `lake env lean`, after the build and under its hold.
--
-- For every constant of the programme's modules (a module whose name is not of Lean, Mathlib or the libraries named in `libRoots`) it writes
-- one JSON record to out/closure.jsonl: the name (n), the module (m), the kind (k), the declaration's line (l), the type's class (t: types
-- equal up to bound-variable names share one class; h the type's hash), the axioms (a) by Lean.collectAxioms -- the traversal `#print axioms`
-- makes -- the type's binders (b: name, whether a Prop, the programme constants the binder's type names), and the closure (c): the same
-- traversal (a constant's type; the value of a definition, a theorem or an opaque; an inductive's constructors) widened from the axioms to every
-- programme constant reached. A library constant reaches no programme constant, so the traversal stops at the library's edge. The last record
-- is a header: the record count and the programme modules read. The file carries no proof and no axiom; the compiler's output is the verdict.
open Lean Elab Command Meta

def libRoots : List Name :=
  [`Init, `Lean, `Std, `Lake, `Mathlib, `Batteries, `Aesop, `Qq, `ProofWidgets, `Plausible, `ImportGraph, `LeanSearchClient]

def isLibModule (m : Name) : Bool := libRoots.any (fun r => r.isPrefixOf m)

def usedBy (ci : ConstantInfo) : Array Name :=
  let t := ci.type.getUsedConstants
  match ci with
  | .defnInfo v => t ++ v.value.getUsedConstants
  | .thmInfo v => t ++ v.value.getUsedConstants
  | .opaqueInfo v => t ++ v.value.getUsedConstants
  | .inductInfo v => t ++ v.ctors.toArray
  | _ => t

def closureOf (env : Environment) (prog : NameSet) (root : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack : Array Name := #[root]
  while stack.size > 0 do
    let c := stack.back!
    stack := stack.pop
    unless seen.contains c do
      seen := seen.insert c
      if let some ci := env.find? c then
        for d in usedBy ci do
          if prog.contains d && !seen.contains d then
            stack := stack.push d
  return seen

def kindOf : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "def"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"
  | .quotInfo _ => "quot"

def keepName (c : Name) : Bool := !c.isInternal || isPrivateName c

set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  let env ← getEnv
  let mods := env.header.moduleNames
  let mut prog : NameSet := {}
  let mut progMods : Array String := #[]
  for i in [0:mods.size] do
    let m := mods[i]!
    if isLibModule m then continue
    progMods := progMods.push m.toString
    for c in env.header.moduleData[i]!.constNames do
      prog := prog.insert c
  let h ← IO.FS.Handle.mk "out/closure.jsonl" IO.FS.Mode.write
  let mut groups : Std.HashMap Expr Nat := {}
  let mut n : Nat := 0
  for i in [0:mods.size] do
    let m := mods[i]!
    if isLibModule m then continue
    for c in env.header.moduleData[i]!.constNames do
      unless keepName c do continue
      let some ci := env.find? c | continue
      let g := (groups.get? ci.type).getD groups.size
      unless groups.contains ci.type do
        groups := groups.insert ci.type g
      let cl := ((closureOf env prog c).toList.filter (fun d => d != c && keepName d)).map (·.toString)
      let axs ← Lean.collectAxioms c
      let line := (← findDeclarationRanges? c).map (·.range.pos.line)
      let binders : MetaM (List Json) :=
        forallTelescope ci.type fun xs _ => xs.toList.mapM fun x => do
          let d ← x.fvarId!.getDecl
          let p ← isProp d.type
          let cs := (d.type.getUsedConstants.filter prog.contains).toList.map (·.toString)
          pure (Json.arr #[toJson d.userName.toString, toJson p, toJson cs])
      let bs : List Json ← (tryCatch binders (fun _ => pure []) : MetaM (List Json))
      let j := Json.mkObj [("n", toJson c.toString), ("m", toJson m.toString), ("k", toJson (kindOf ci)), ("l", toJson line),
        ("t", toJson g), ("h", toJson ci.type.hash.toNat), ("a", toJson (axs.toList.map (·.toString))), ("b", Json.arr bs.toArray),
        ("c", toJson cl)]
      h.putStrLn j.compress
      n := n + 1
  h.putStrLn (Json.mkObj [("header", toJson true), ("records", toJson n), ("modules", toJson progMods.toList)]).compress
  h.flush
  logInfo m!"closure records {n} ; programme modules {progMods.size}"
