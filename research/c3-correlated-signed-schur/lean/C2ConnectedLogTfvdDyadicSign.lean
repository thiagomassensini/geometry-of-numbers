import C2ConnectedDyadicKernelIndefinite
import CPFormal.Analytic.CpC2DirichletJetTfvd
import Mathlib.Tactic

/-!
The already EXISTING source-accurate finite TFVD/Dirichlet bridge carries
the negative sign of the C2 odd-core connected semiprime coefficient
through EVERY cutoff 60*2^k. This is a finite arithmetic/log readout,
not a completed F(z) positive moment Hankel matrix.
-/

namespace CarryWheelNativeSignedGate
open CPFormal.Analytic.Cp

theorem dyadic_c2_b15_negative (k : ℕ) :
    c2OddCoreLogCoefficient (60*2^k) 15 < 0 := by
  have hformula := c2OddCoreLogCoefficient_distinct_primes
    (60*2^k) (p:=3) (q:=5)
    (by norm_num) (by decide) (by norm_num) (by decide) (by norm_num)
  have hlog : 0 < Real.log (15 : ℝ) :=
    Real.log_pos (by norm_num)
  have hd : c2OddCoreConnectedCumulantReal (60*2^k) 3 5 < 0 := by
    unfold c2OddCoreConnectedCumulantReal
    exact_mod_cast dyadic_c2_connected_3_5_strictly_negative k
  simpa only [show (3*5:ℕ)=15 by norm_num] using
    (hformula.symm ▸ (mul_neg_of_pos_of_neg hlog hd))

/-- The finite C2 TFVD log-gap at spectral variable s=0 is exactly
the negative, genuine connected b_T(15), not an inserted source. -/
theorem dyadic_c2_tfvd_log_readout_eq_b15 (block k : ℕ)
    {kappa omega : ℂ} (hkappa : kappa ≠ 0) (homega : omega ≠ 0) :
    c2OddCoreDirichletLogTfvdReadout block kappa omega
      (60*2^k) 3 5 0 =
        (c2OddCoreLogCoefficient (60*2^k) 15 : ℂ) := by
  have h := c2OddCoreDirichletLogTfvdReadout_eq_logCoefficient_mul
    block hkappa homega (60*2^k)
    (p:=3) (q:=5)
    (by norm_num) (by decide) (by norm_num) (by decide) (by norm_num) 0
  simpa [natDirichletTerm, dirichletTerm] using h

/-- Consequently the real part of the source-accurate finite TFVD
readout is negative throughout the entire dyadic tower. -/
theorem dyadic_c2_tfvd_log_readout_re_negative (block k : ℕ)
    {kappa omega : ℂ} (hkappa : kappa ≠ 0) (homega : omega ≠ 0) :
    (c2OddCoreDirichletLogTfvdReadout block kappa omega
      (60*2^k) 3 5 0).re < 0 := by
  rw [dyadic_c2_tfvd_log_readout_eq_b15 block k hkappa homega]
  simpa only [Complex.ofReal_re] using dyadic_c2_b15_negative k

end CarryWheelNativeSignedGate
