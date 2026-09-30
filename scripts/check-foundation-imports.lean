import Lean

/-! Parse actual Lean headers, including multiline and meta imports. The discrete
root and every foundational source can depend only on Init and Foundation.
The audit alone may also import Lean and the discrete root. -/

def main : IO Unit := do
  let sources ← (System.FilePath.mk "GeometryOfNumbers/Foundation").walkDir
  let sources := sources.push "GeometryOfNumbers.lean"
  for source in sources do
    if source.extension == some "lean" then
      let (imports, _, messages) ← Lean.Elab.parseImports (← IO.FS.readFile source)
        (some source.toString)
      if messages.hasErrors then
        throw <| IO.userError s!"Cannot parse imports: {source}"
      for dependency in imports do
        let name := dependency.module.toString
        let allowed := name == "Init" || name.startsWith "GeometryOfNumbers.Foundation." ||
          (source.toString == "GeometryOfNumbers/Foundation/Audit.lean" &&
            (name == "Lean" || name == "GeometryOfNumbers"))
        unless allowed do
          throw <| IO.userError s!"Foundation import boundary violated: {source} -> {name}"
  IO.println "PASS: discrete imports isolated (audit tooling excepted); no Analysis or Mathlib."
