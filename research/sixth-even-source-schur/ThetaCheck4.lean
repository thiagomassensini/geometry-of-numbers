import ThetaTwentyTwo
namespace CarrySixthEven
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 48000000

theorem theta_input_check_4 :
    (CarryIntegralCertificate.tabledFullThetaMomentBox 8).contained (thetaInputBox 4) = true := by
  decide +kernel

end CarrySixthEven
