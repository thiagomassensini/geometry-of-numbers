import EulerGamma
import CompletedTraceJets

namespace CarryC3Gamma
open MeasureTheory Set Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

/-- Finite evaluator for the original Gamma, not a replacement source. -/
def gammaFinite (N : ℕ) (T : ℝ) (z : ℂ) : ℂ :=
  (T:ℂ)^z * ∑ k ∈ Finset.range N,
    (-(T:ℂ))^k/((k.factorial:ℂ)*(z+k))

theorem euler_term (k : ℕ) (z : ℂ) (x : ℝ) (hx : 0 < x) :
    (-(x:ℂ))^k/(k.factorial:ℂ)*(x:ℂ)^(z-1) =
      (-1:ℂ)^k/(k.factorial:ℂ)*(x:ℂ)^(z+k-1) := by
  have hx0 : (x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  rw [show z+(k:ℂ)-1=(k:ℂ)+(z-1) by ring,Complex.cpow_add _ _ hx0,
    Complex.cpow_natCast,neg_pow]
  ring

theorem gamma_head_integral_formula (N : ℕ) (T : ℝ) (hT : 0 < T)
    (z : ℂ) (hz : 0 < z.re) : gammaHeadIntegral N T z = gammaFinite N T z := by
  have he : gammaHeadIntegral N T z = ∫ x : ℝ in 0..T,
      ∑ k ∈ Finset.range N, (-1:ℂ)^k/(k.factorial:ℂ)*(x:ℂ)^(z+k-1) := by
    unfold gammaHeadIntegral expHead
    apply intervalIntegral.integral_congr_ae
    filter_upwards with x hx
    have hx' : 0 < x := by simpa [min_eq_left hT.le] using hx.1
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun k _ => euler_term k z x hx')
  rw [he,intervalIntegral.integral_finsetSum]
  · unfold gammaFinite
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hzk : z+(k:ℂ) ≠ 0 := by
      intro hh
      have hr := congrArg Complex.re hh
      simp only [Complex.add_re,Complex.natCast_re,Complex.zero_re] at hr
      have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    rw [intervalIntegral.integral_const_mul,integral_cpow (Or.inl (by
      simp only [Complex.sub_re,Complex.add_re,Complex.natCast_re,Complex.one_re]
      linarith [Nat.cast_nonneg (α:=ℝ) k])),sub_add_cancel,Complex.ofReal_zero,
      Complex.zero_cpow hzk,sub_zero,Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hT.ne'),
      Complex.cpow_natCast,neg_pow]
    field_simp
    ring
  · intro k hk
    exact (intervalIntegral.intervalIntegrable_cpow' (by
      simp only [Complex.sub_re,Complex.add_re,Complex.natCast_re,Complex.one_re]
      linarith [Nat.cast_nonneg (α:=ℝ) k])).const_mul _

theorem gamma_finite_error (N : ℕ) (T : ℝ) (hT : 1 ≤ T)
    (hN : T/(N+1:ℕ) ≤ 1/2) (z : ℂ) (hz : 0 < z.re) (hz1 : z.re ≤ 1) :
    ‖Complex.Gamma z-gammaFinite N T z‖ ≤
      2*T^(N+1)/((N.factorial:ℝ)*z.re)+Real.exp (-T) := by
  rw [← gamma_head_integral_formula N T (by linarith) z hz]
  exact gamma_integral_approx_error N T hT hN z hz hz1

end
end CarryC3Gamma
