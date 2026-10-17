import ThetaTwentyTwo
namespace CarrySixthEven
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 48000000

theorem theta_input_check_10 :
    (CarryIntegralCertificate.tabledFullThetaMomentBox 20).contained (thetaInputBox 10) = true := by
  decide +kernel

end CarrySixthEven
