import ThetaCheck0
import ThetaCheck1
import ThetaCheck2
import ThetaCheck3
import ThetaCheck4
import ThetaCheck5
import ThetaCheck6
import ThetaCheck7
import ThetaCheck8
import ThetaCheck9
import ThetaCheck10
import ThetaCheck11

namespace CarrySixthEven
open CarryIntegralCertificate CarrySelfAdjointOperator
set_option autoImplicit false
set_option maxRecDepth 65536

theorem theta_input_checks (j : Fin 12) :
    (tabledFullThetaMomentBox (2*j.val)).contained (thetaInputBox j.val) = true := by
  fin_cases j
  · exact theta_input_check_0
  · exact theta_input_check_1
  · exact theta_input_check_2
  · exact theta_input_check_3
  · exact theta_input_check_4
  · exact theta_input_check_5
  · exact theta_input_check_6
  · exact theta_input_check_7
  · exact theta_input_check_8
  · exact theta_input_check_9
  · exact theta_input_check_10
  · exact theta_input_check_11

theorem mem_thetaInputBox (n : ℕ) :
    (thetaInputBox n).Mem (completedNativeThetaTailMoment (2*n)) := by
  by_cases hn : n < 12
  · exact mem_of_contained (mem_tabledTheta_upto_twentyTwo (2*n) (by omega))
      (theta_input_checks ⟨n,hn⟩)
  · simp only [thetaInputBox,dif_neg hn,Box.Mem]

end CarrySixthEven
