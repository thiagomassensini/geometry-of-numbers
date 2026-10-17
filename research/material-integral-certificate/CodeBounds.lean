import CoefficientCode

namespace CarryIntegralCertificate
open CarrySelfAdjointOperator Real Set Filter MeasureTheory Polynomial
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def thetaCodeMajorant (n : ℕ) (Q : ℝ) : ℝ :=
  ∑ r ∈ Finset.range (n+1), |((thetaCoefficientCode n)[r]?.getD 0:ℝ)| *Q^r

theorem thetaCode_eval (n : ℕ) (hn : n ≤ 16) (q : ℝ) :
    aeval q (thetaDerivativePolynomial n) =
      ∑ r ∈ Finset.range (n+1), ((thetaCoefficientCode n)[r]?.getD 0:ℝ)*q^r := by
  rw [thetaPolynomialCode_correct n hn]
  simp only [thetaPolynomialCode,map_sum,map_mul,map_pow,aeval_C,aeval_X]
  rfl

theorem thetaCode_abs_le (n : ℕ) (hn : n ≤ 16) {q Q : ℝ}
    (hq : 0 ≤ q) (hqQ : q ≤ Q) :
    |aeval q (thetaDerivativePolynomial n)| ≤ thetaCodeMajorant n Q := by
  rw [thetaCode_eval n hn]
  calc
    _ ≤ ∑ r ∈ Finset.range (n+1), |((thetaCoefficientCode n)[r]?.getD 0:ℝ)*q^r| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro r _
      rw [abs_mul,abs_pow,abs_of_nonneg hq]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq hqQ r) (abs_nonneg _)

theorem thetaCode_cell_bound (m n : ℕ) (hn : n ≤ 16) (a b : ℝ) (ha : 0 ≤ a) :
    ∀ x ∈ Icc a b, |thetaModeDerivative m n x| ≤
      thetaCodeMajorant n (thetaArgument m b)*thetaMode m a := by
  intro x hx
  have hq : 0 ≤ thetaArgument m x := by unfold thetaArgument; positivity
  have hqx : thetaArgument m x ≤ thetaArgument m b := by
    unfold thetaArgument
    gcongr
    exact hx.2
  have hp := thetaCode_abs_le n hn hq hqx
  have hf : thetaMode m x ≤ thetaMode m a :=
    thetaMode_antitone m ha (ha.trans hx.1) hx.1
  unfold thetaModeDerivative
  rw [abs_mul,abs_of_nonneg (thetaMode_nonneg m x)]
  exact mul_le_mul hp hf (thetaMode_nonneg m x) ((abs_nonneg _).trans hp)

end
end CarryIntegralCertificate
