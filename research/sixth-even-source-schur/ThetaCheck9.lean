import ThetaTwentyTwo
namespace CarrySixthEven
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 48000000

theorem theta_input_check_9 :
    (CarryIntegralCertificate.tabledFullThetaMomentBox 18).contained (thetaInputBox 9) = true := by
  decide +kernel

end CarrySixthEven
