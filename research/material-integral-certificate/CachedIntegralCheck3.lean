import TabledSourceProgram
import PivotFromIntegral
namespace CarryIntegralCertificate
set_option maxRecDepth 65536
set_option maxHeartbeats 48000000

theorem cached_integral_checks_3 :
    ((tabledFullThetaMomentBox 6).contained (momentInputTable 3) = true) ∧
    ((tabledFullThetaMomentBox 14).contained (momentInputTable 7) = true) := by
  decide +kernel

end CarryIntegralCertificate
