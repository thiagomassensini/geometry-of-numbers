import GeometryOfNumbers.Analysis.MomentScaleElimination

/-! Scaling the completed response coefficients and THEN taking its log
derivative fixes the moment mass factor. A constant amplitude cancels. -/
namespace GeometryOfNumbers.Analysis.CarryScale
open FiniteClockHeightLedger
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem log_sequence_dilate (phi h : ℕ → ℝ) (beta q : ℝ)
    (hr : IsLogDerivativeMomentSequence phi h) :
    IsLogDerivativeMomentSequence (fun n => beta*q^n*phi n)
      (fun r => q^(r+1)*h r) := by
  intro n
  have hs : (∑ k ∈ Finset.range n, (q^(k+1)*h k)*(beta*q^(n-k)*phi (n-k))) =
      beta*q^(n+1)*∑ k ∈ Finset.range n, h k*phi (n-k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have he : (k+1)+(n-k)=n+1 := by have := Finset.mem_range.mp hk; omega
    calc
      _ = beta*(q^(k+1)*q^(n-k))*(h k*phi (n-k)) := by ring
      _ = _ := by rw [← pow_add, he]
  simp only [pow_zero, mul_one]
  rw [hs]
  nlinarith [congrArg (fun x : ℝ => beta*q^(n+1)*x) (hr n)]

theorem log_moments_dilate (phi : ℕ → ℝ) (beta q : ℝ)
    (hb : beta ≠ 0) (hp : phi 0 ≠ 0) :
    finiteLogMoment (fun n => beta*q^n*phi n) =
      (fun r => q^(r+1)*finiteLogMoment phi r) := by
  exact (finiteLogMoment_isSequence _ (by simpa using mul_ne_zero hb hp)).unique
    (by simpa using mul_ne_zero hb hp)
    (log_sequence_dilate phi _ beta q (finiteLogMoment_isSequence phi hp))

theorem log_moments_constant_amplitude (phi : ℕ → ℝ) (beta : ℝ)
    (hb : beta ≠ 0) (hp : phi 0 ≠ 0) :
    finiteLogMoment (fun n => beta*phi n) = finiteLogMoment phi := by
  simpa using log_moments_dilate phi beta 1 hb hp

/-- The extra q comes from the derivative, not from amplitude normalization. -/
theorem response_dilation_mass (phi : ℕ → ℝ) (beta q : ℝ)
    (hb : beta ≠ 0) (hp : phi 0 ≠ 0) :
    finiteLogMoment (fun n => beta*q^n*phi n) =
      massScaledMoment q q (finiteLogMoment phi) := by
  rw [log_moments_dilate phi beta q hb hp]
  funext r
  simp [massScaledMoment, scaledMoment, pow_succ]
  ring

/-- Uniform mass q^-1 in the symbolic test is NOT induced by multiplying
and dilating a nonconstant log response, except at the trivial q=1. -/
theorem geometric_mass_not_response_dilation (h : ℕ → ℝ) (q : ℝ)
    (hq : 0 < q) (hne : q ≠ 1) (h0 : h 0 ≠ 0) :
    massScaledMoment q⁻¹ q h ≠ massScaledMoment q q h := by
  intro he
  have hz := congrFun he 0
  simp only [massScaledMoment, scaledMoment, pow_zero, one_mul] at hz
  have heq : q⁻¹ = q := mul_right_cancel₀ h0 hz
  have hh := congrArg (fun x : ℝ => q*x) heq
  rw [mul_inv_cancel₀ hq.ne'] at hh
  have : q = 1 := by nlinarith
  exact hne this

/-- A common phase on a COMPLETED response is retained explicitly. This
lemma does not assert that a physical dilation transports its completion. -/
theorem log_response_phase (F g : ℝ → ℂ) (t omega : ℝ)
    (hF : DifferentiableAt ℝ F t) (hg : HasDerivAt g (-Complex.I*(omega:ℂ)*g t) t)
    (hFn : F t ≠ 0) (hgn : g t ≠ 0) :
    -deriv (fun u => g u*F u) t / (2*(g t*F t)) =
      -deriv F t / (2*F t) + Complex.I*(omega:ℂ)/2 := by
  have hh : HasDerivAt (fun u => g u*F u)
      ((-Complex.I*(omega:ℂ)*g t)*F t+g t*deriv F t) t := hg.mul hF.hasDerivAt
  rw [hh.deriv]
  field_simp [hFn, hgn]
  ring

end
end GeometryOfNumbers.Analysis.CarryScale
