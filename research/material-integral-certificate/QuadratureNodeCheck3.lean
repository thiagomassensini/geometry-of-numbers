import QuadratureCacheData
namespace CarryIntegralCertificate
set_option maxRecDepth 65536
set_option maxHeartbeats 48000000

theorem quadrature_node_checks_3 : ∀ m : Fin 3,
    ∀ j : Fin (thetaCertificateCellCount m.val/4),
    (∀ r : Fin 16, quadratureCoefficientComputation m.val (4*j.val+3) r.val =
      cachedQuadratureCoefficient m.val (4*j.val+3) r.val) ∧
    quadratureErrorComputation m.val (4*j.val+3) = cachedQuadratureError m.val (4*j.val+3) := by
  decide +kernel

end CarryIntegralCertificate
