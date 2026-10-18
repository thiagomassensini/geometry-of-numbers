import ThetaTwentyTwo
namespace CarrySixthEven
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 48000000

theorem theta_input_check_11 :
    (CarryIntegralCertificate.tabledFullThetaMomentBox 22).contained (thetaInputBox 11) = true := by
  decide +kernel

end CarrySixthEven
