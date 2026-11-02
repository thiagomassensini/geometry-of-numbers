import EffectivePairBounds
import Mathlib.Analysis.Complex.RealDeriv

namespace CarrySummableRadial
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryOddCauchy
open CarryEffectiveRadial CarryAllOrderTail CarryMovingRadial NativeLaguerre
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

def pairCorrection (r s : ℕ) : ℂ :=
  spatialCorrection (2*r+1) (2*s+1)*(h (r+s+2):ℂ)

def pairTail (r s : ℕ) (z : ℂ) : ℂ :=
  oddPairKernel (effectiveRemainderSamples (r+s+3) z) r s

def pairTailVelocity (r s : ℕ) (z : ℂ) : ℂ :=
  oddPairTailDerivative (r+s+3) r s z

def effectivePairCurve (r s : ℕ) (z : ℂ) : ℂ :=
  (h (r+s+1):ℂ) - z^2*pairCorrection r s + z^4*pairTail r s z

def pairConstant (r s : ℕ) : ℝ :=
  ‖spatialCorrection (2*r+1) (2*s+1)‖ +
  (oddFilterBudget r s (2*(r+s+3)+1)+oddFilterBudget s r (2*(r+s+3)+1)) +
  (oddFilterBudget r s (2*(r+s+3)+2)+oddFilterBudget s r (2*(r+s+3)+2))

theorem pair_constant_nonneg (r s : ℕ) : 0 ≤ pairConstant r s := by
  unfold pairConstant
  have h1 := odd_filter_budget_nonneg r s (2*(r+s+3)+1)
  have h2 := odd_filter_budget_nonneg s r (2*(r+s+3)+1)
  have h3 := odd_filter_budget_nonneg r s (2*(r+s+3)+2)
  have h4 := odd_filter_budget_nonneg s r (2*(r+s+3)+2)
  positivity

theorem pair_curve_hasDerivAt (r s : ℕ) (z : ℂ)
    (hz : ∀ j < 2*max r s+2, ‖((j+1:ℕ):ℂ)*z‖ < 1) :
    HasDerivAt (effectivePairCurve r s)
      (-2*z*pairCorrection r s+4*z^3*pairTail r s z+z^4*pairTailVelocity r s z) z := by
  have ht : HasDerivAt (pairTail r s) (pairTailVelocity r s z) z :=
    odd_pair_tail_hasDerivAt (r+s+3) r s z hz
  have hd := ((hasDerivAt_const z (h (r+s+1):ℂ)).sub
    (((hasDerivAt_id z).pow 2).mul_const (pairCorrection r s))).add
      (((hasDerivAt_id z).pow 4).mul ht)
  convert hd using 1
  all_goals try rfl
  all_goals (simp [Pi.pow_apply]; ring)

theorem pair_curve_derivative_bound (r s : ℕ) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hz : ∀ j < 2*max r s+2, ‖((j+1:ℕ):ℂ)*(t:ℂ)‖ ≤ 1/4) :
    |deriv (fun x : ℝ => (effectivePairCurve r s (x:ℂ)).re) t| ≤
      2*pairConstant r s*t := by
  have hz' : ∀ j < 2*max r s+2, ‖((j+1:ℕ):ℂ)*(t:ℂ)‖ < 1 := by
    intro j hj; have := hz j hj; linarith
  have ha := pair_curve_hasDerivAt r s (t:ℂ) hz'
  have hreal := ha.real_of_complex
  have hb := odd_pair_effective_tail_bound (r+s+3) r s (t:ℂ) hz'
  have hv := odd_pair_tail_derivative_bound (r+s+3) r s (t:ℂ) hz
  have ha' := (Complex.abs_re_le_norm
    (-2*(t:ℂ)*pairCorrection r s+4*(t:ℂ)^3*pairTail r s (t:ℂ)+
      (t:ℂ)^4*pairTailVelocity r s (t:ℂ)))
  rw [hreal.deriv]
  apply ha'.trans
  have hnorm : ‖-2*(t:ℂ)*pairCorrection r s+4*(t:ℂ)^3*pairTail r s (t:ℂ)+
      (t:ℂ)^4*pairTailVelocity r s (t:ℂ)‖ ≤
      2*t*‖pairCorrection r s‖+4*t^3*‖pairTail r s (t:ℂ)‖+
        t^4*‖pairTailVelocity r s (t:ℂ)‖ := by
    have h := (norm_add_le
      (-2*(t:ℂ)*pairCorrection r s+4*(t:ℂ)^3*pairTail r s (t:ℂ))
      ((t:ℂ)^4*pairTailVelocity r s (t:ℂ))).trans
      (add_le_add (norm_add_le (-2*(t:ℂ)*pairCorrection r s)
        (4*(t:ℂ)^3*pairTail r s (t:ℂ))) le_rfl)
    simpa [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht,
      norm_neg] using h
  apply hnorm.trans
  have htail : 0 ≤ oddFilterBudget r s (2*(r+s+3)+1)+oddFilterBudget s r (2*(r+s+3)+1) :=
    add_nonneg (odd_filter_budget_nonneg _ _ _) (odd_filter_budget_nonneg _ _ _)
  have hvel : 0 ≤ oddFilterBudget r s (2*(r+s+3)+2)+oddFilterBudget s r (2*(r+s+3)+2) :=
    add_nonneg (odd_filter_budget_nonneg _ _ _) (odd_filter_budget_nonneg _ _ _)
  have hb' := mul_le_mul_of_nonneg_left hb (show 0 ≤ 4*t^3 by positivity)
  have hv' := mul_le_mul_of_nonneg_left hv (show 0 ≤ t^4 by positivity)
  have ht3 : t^3 ≤ t := by nlinarith [sq_nonneg (t-1), sq_nonneg t, mul_nonneg ht (show 0 ≤ 1-t by linarith)]
  have ht4 : t^4 ≤ t := by nlinarith [sq_nonneg (t^2-t),sq_nonneg t, sq_nonneg (1-t^2)]
  have hbt := mul_le_mul_of_nonneg_left ht3 htail
  have hvt := mul_le_mul_of_nonneg_left ht4 hvel
  have hmoment : ‖(h (r+s+2):ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact (source_coefficient_bound (r+s+2)).trans
      (pow_le_one₀ (by norm_num) (by norm_num))
  have hcorr : ‖pairCorrection r s‖ ≤ ‖spatialCorrection (2*r+1) (2*s+1)‖ := by
    unfold pairCorrection
    rw [norm_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hmoment
      (norm_nonneg (spatialCorrection (2*r+1) (2*s+1)))
  have hct := mul_le_mul_of_nonneg_left hcorr (show 0 ≤ 2*t by positivity)
  dsimp only [pairTail, pairTailVelocity] at *
  unfold pairConstant
  nlinarith

end
end CarrySummableRadial
