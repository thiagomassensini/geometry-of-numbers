import CachedIntegralChecks
import TabledSourceEquivalence

namespace CarryIntegralCertificate
set_option autoImplicit false

/-- The source nodes and the exact rational grid weights are independently
identified with the source. The ten final inclusions are kernel-checked. -/
theorem integral_input_checks : ∀ k : Fin 10,
    (tabledFullThetaMomentBox (2*k.val)).contained (momentInputTable k) = true :=
  cached_integral_input_checks

end CarryIntegralCertificate
