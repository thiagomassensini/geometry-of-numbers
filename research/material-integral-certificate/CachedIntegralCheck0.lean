import TabledSourceProgram
import PivotFromIntegral
namespace CarryIntegralCertificate
set_option maxRecDepth 65536
set_option maxHeartbeats 48000000

theorem cached_integral_checks_0 :
    ((tabledFullThetaMomentBox 0).contained (momentInputTable 0) = true) ∧
    ((tabledFullThetaMomentBox 8).contained (momentInputTable 4) = true) ∧
    ((tabledFullThetaMomentBox 16).contained (momentInputTable 8) = true) := by
  decide +kernel

end CarryIntegralCertificate
