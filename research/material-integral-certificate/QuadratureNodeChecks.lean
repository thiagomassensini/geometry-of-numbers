import QuadratureNodeCheck0
import QuadratureNodeCheck1
import QuadratureNodeCheck2
import QuadratureNodeCheck3

namespace CarryIntegralCertificate
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem quadrature_node_checks (m : Fin 3) (j : Fin (thetaCertificateCellCount m.val)) :
    (∀ r : Fin 16, quadratureCoefficientComputation m.val j.val r.val =
      cachedQuadratureCoefficient m.val j.val r.val) ∧
    quadratureErrorComputation m.val j.val = cachedQuadratureError m.val j.val := by
  have hj := j.isLt
  have hd : j.val/4 < thetaCertificateCellCount m.val/4 := by
    fin_cases m <;> norm_num [thetaCertificateCellCount] at hj ⊢ <;> omega
  by_cases h0 : j.val%4=0
  · have he : 4*(j.val/4)+0=j.val := by omega
    simpa only [he] using quadrature_node_checks_0 m ⟨j.val/4,hd⟩
  by_cases h1 : j.val%4=1
  · have he : 4*(j.val/4)+1=j.val := by omega
    simpa only [he] using quadrature_node_checks_1 m ⟨j.val/4,hd⟩
  by_cases h2 : j.val%4=2
  · have he : 4*(j.val/4)+2=j.val := by omega
    simpa only [he] using quadrature_node_checks_2 m ⟨j.val/4,hd⟩
  · have he : 4*(j.val/4)+3=j.val := by omega
    simpa only [he] using quadrature_node_checks_3 m ⟨j.val/4,hd⟩

end CarryIntegralCertificate
