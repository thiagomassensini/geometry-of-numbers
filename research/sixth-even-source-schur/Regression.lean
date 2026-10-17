import SixthEvenCertificate
import VariationalSchur

namespace CarrySixthEven
open CarrySelfAdjointOperator CarryThetaPattern
open MeasureTheory
set_option autoImplicit false

/-- The literal signed source inequality, including the complete old feedback. -/
theorem sixth_even_literal_theta_gate :
    -4*(Nat.factorial 22:ℝ)*sourceCeiling 0 5 <
      1848*completedNativeThetaTailMoment 20-completedNativeThetaTailMoment 22 := by
  have hg := sixth_even_theta_integral_certificate
  rw [sourceThetaIntegral_moments] at hg
  norm_num only [Nat.reduceMul,Nat.reduceAdd,Nat.cast_ofNat] at hg ⊢
  exact hg

theorem sixth_even_integral_gate :
    -4*(Nat.factorial 22:ℝ)*sourceCeiling 0 5 <
      ∫ u in Set.Ioi (0:ℝ),
        (1848*u^20-u^22)*XiThetaCosine.thetaTail u := by
  have hg := sixth_even_theta_integral_certificate
  norm_num only [sourceThetaIntegral,Nat.reduceMul,Nat.reduceAdd,Nat.cast_ofNat] at hg ⊢
  exact hg

end CarrySixthEven
