import TaylorNodeComputation

/-! Untrusted witnesses; TaylorNodeChecks verify the complete table in the kernel. -/
open CarryIntegralCertificate Lean
private def boxJson : Box → Json
  | .all => Json.null
  | .finite a b => Json.arr #[toJson (toString a),toJson (toString b)]
#eval do
  let rows := (List.range 3).flatMap fun m =>
    (List.range (thetaCertificateCellCount m)).map fun j =>
      Json.mkObj [("m",toJson m),("j",toJson j),
        ("coefficients",toJson ((List.range 16).map (fun r => boxJson (quadratureCoefficientComputation m j r)))),
        ("error",boxJson (quadratureErrorComputation m j))]
  IO.println ((toJson rows).compress)
