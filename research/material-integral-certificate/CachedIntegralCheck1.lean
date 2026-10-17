import TabledSourceProgram
import PivotFromIntegral
namespace CarryIntegralCertificate
set_option maxRecDepth 65536
set_option maxHeartbeats 48000000

theorem cached_integral_checks_1 :
    ((tabledFullThetaMomentBox 2).contained (momentInputTable 1) = true) ∧
    ((tabledFullThetaMomentBox 10).contained (momentInputTable 5) = true) ∧
    ((tabledFullThetaMomentBox 18).contained (momentInputTable 9) = true) := by
  decide +kernel

end CarryIntegralCertificate
