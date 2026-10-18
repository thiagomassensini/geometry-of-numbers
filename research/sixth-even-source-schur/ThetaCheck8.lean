import ThetaTwentyTwo
namespace CarrySixthEven
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 48000000

theorem theta_input_check_8 :
    (CarryIntegralCertificate.tabledFullThetaMomentBox 16).contained (thetaInputBox 8) = true := by
  decide +kernel

end CarrySixthEven
