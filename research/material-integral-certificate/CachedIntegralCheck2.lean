import TabledSourceProgram
import PivotFromIntegral
namespace CarryIntegralCertificate
set_option maxRecDepth 65536
set_option maxHeartbeats 48000000

theorem cached_integral_checks_2 :
    ((tabledFullThetaMomentBox 4).contained (momentInputTable 2) = true) ∧
    ((tabledFullThetaMomentBox 12).contained (momentInputTable 6) = true) := by
  decide +kernel

end CarryIntegralCertificate
