import ThetaTwentyTwo
namespace CarrySixthEven
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 48000000

theorem theta_input_check_6 :
    (CarryIntegralCertificate.tabledFullThetaMomentBox 12).contained (thetaInputBox 6) = true := by
  decide +kernel

end CarrySixthEven
