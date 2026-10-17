import CachedIntegralCheck0
import CachedIntegralCheck1
import CachedIntegralCheck2
import CachedIntegralCheck3

namespace CarryIntegralCertificate
set_option autoImplicit false
attribute [local irreducible] tabledFullThetaMomentBox momentInputTable

theorem cached_integral_input_checks : ∀ k : Fin 10,
    (tabledFullThetaMomentBox (2*k.val)).contained (momentInputTable k) = true := by
  intro k
  fin_cases k
  · exact cached_integral_checks_0.1
  · exact cached_integral_checks_1.1
  · exact cached_integral_checks_2.1
  · exact cached_integral_checks_3.1
  · exact cached_integral_checks_0.2.1
  · exact cached_integral_checks_1.2.1
  · exact cached_integral_checks_2.2
  · exact cached_integral_checks_3.2
  · exact cached_integral_checks_0.2.2
  · exact cached_integral_checks_1.2.2

end CarryIntegralCertificate
