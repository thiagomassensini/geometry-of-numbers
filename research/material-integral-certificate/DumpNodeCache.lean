import SourceComputation

/-! Untrusted witness exporter. Every output entry is independently checked
by the kernel in ArgNodeChecks and ModeNodeChecks. -/
open CarryIntegralCertificate Lean

private def cacheCellCount (m : ℕ) : ℕ := match m with
  | 0 => 96 | 1 => 64 | 2 => 48 | _ => 0

private def boxJson : Box → Json
  | .all => Json.null
  | .finite a b => Json.arr #[toJson (toString a),toJson (toString b)]

#eval do
  let rows := (List.range 3).flatMap fun m =>
    (List.range (cacheCellCount m+1)).map fun j =>
      Json.mkObj [("m",toJson m),("j",toJson j),
        ("q",boxJson (argumentBox m (gridBox j 64))),
        ("f",boxJson (modeBox m (gridBox j 64)))]
  IO.println ((toJson rows).compress)
