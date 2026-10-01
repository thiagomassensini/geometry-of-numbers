import Lean

/-! Geometry may use Init, the frozen Foundation and itself. Only audit tooling
may use Lean. Neither analysis nor historical libraries may feed back into it. -/

def main : IO Unit := do
  let sources ← (System.FilePath.mk "GeometryOfNumbers/Geometry").walkDir
  let sources := sources.push "GeometryOfNumbers/Geometry.lean"
  for source in sources do
    if source.extension == some "lean" then
      let (imports, _, messages) ← Lean.Elab.parseImports (← IO.FS.readFile source)
        (some source.toString)
      if messages.hasErrors then
        throw <| IO.userError s!"Cannot parse imports: {source}"
      for dependency in imports do
        let name := dependency.module.toString
        let allowed := name == "Init" || name == "GeometryOfNumbers" ||
          name.startsWith "GeometryOfNumbers.Foundation." ||
          name.startsWith "GeometryOfNumbers.Geometry." ||
          name == "GeometryOfNumbers.Geometry" ||
          (source.toString == "GeometryOfNumbers/Geometry/Audit.lean" && name == "Lean")
        unless allowed do
          throw <| IO.userError s!"Geometry import boundary violated: {source} -> {name}"
  IO.println "PASS: Geometry imports only Init/Foundation/Geometry (audit tooling excepted)."
