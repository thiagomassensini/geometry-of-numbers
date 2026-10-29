import ResidualReturn
import CarrySelfAdjointOperator.CompletedNativeChiralReturnLinearizationObstruction

namespace CarryCauchyResidual
open CarrySelfAdjointOperator ChiralReturn CarryReturnDeflation CarryPositiveSquare
open Filter Topology
open scoped InnerProductSpace ComplexConjugate BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000

def radialScale (k : ℕ) : ℂ := (k:ℂ)+1

theorem radialScale_ne_zero (k : ℕ) : radialScale k ≠ 0 := by
  unfold radialScale
  exact_mod_cast (show (k:ℝ)+1 ≠ 0 by positivity)

theorem curvature_eq_four_moment : nativeRadialSourceCurvature =
    4*(canonicalCompletedNativeLogDerivativeMoment 0:ℂ) := by
  rw [canonicalCompletedNativeLogDerivativeMoment_zero_eq_characteristicCurvature_chiral]
  unfold nativeRadialSourceCurvature
  ring

theorem sourceReturn_tendsto (n : ℕ) :
    Tendsto (fun k => sourceReturn k n) atTop (nhds (-1)) := by
  have h := hasDerivAt_completedNativeHermiteBiehlerChiralQuotient_zero.continuousAt.tendsto.comp
    (canonicalCompletedC3RadialTiltPoint_tendsto_zero n)
  simpa only [Function.comp_def, sourceReturn,
    completedNativeHermiteBiehlerChiralQuotient_zero] using h

/-- The scale is the ORIGINAL radial grid scale. Only the already proved
central curvature is used; no positive later pivot is imported. -/
theorem source_tangent (n : ℕ) :
    Tendsto (fun k => (sourceReturn k n+1)*radialScale k) atTop
      (nhds (4*(canonicalCompletedNativeLogDerivativeMoment 0:ℂ)*((n:ℂ)+1))) := by
  have h := (nativeRadialSource_tangent n).const_mul ((n:ℂ)+1)
  rw [curvature_eq_four_moment] at h
  convert h using 1
  · funext k
    have hn : (n:ℂ)+1 ≠ 0 := by exact_mod_cast (show (n:ℝ)+1 ≠ 0 by positivity)
    have hk := radialScale_ne_zero k
    simp only [sourceReturn, canonicalCompletedC3RadialTiltPoint,
      canonicalCompletedC3RadialTiltStep, canonicalGreenJetStep, Nat.cast_add, Nat.cast_one,
      radialScale] at *
    field_simp
  · ring

theorem returnedCoefficient_tangent (n : ℕ) :
    Tendsto (fun k => returnedCoefficient k n*radialScale k) atTop
      (nhds (4*(canonicalCompletedNativeLogDerivativeMoment 0:ℂ)*(n:ℂ))) := by
  have h := (source_tangent n).sub (source_tangent 0)
  convert h using 1
  · funext k
    change (sourceReturn k n-sourceReturn k 0)*radialScale k = _
    ring
  · push_cast
    ring

theorem feedbackDenominator_tangent (n : ℕ) :
    Tendsto (fun k => feedbackDenominator k n*radialScale k) atTop
      (nhds (4*(canonicalCompletedNativeLogDerivativeMoment 0:ℂ)*((n:ℂ)+2))) := by
  have hs := source_tangent n
  have hr := (source_tangent 0).star
  have hz := ((sourceReturn_tendsto 0).add_const 1).star
  have h := (hs.add hr).sub (hz.mul hs)
  have he (k : ℕ) : feedbackDenominator k n*radialScale k =
      (sourceReturn k n+1)*radialScale k + star ((sourceReturn k 0+1)*radialScale k) -
      star (sourceReturn k 0+1)*((sourceReturn k n+1)*radialScale k) := by
    simp [feedbackDenominator, oneReturn, sourceReturn, radialScale]
    ring
  have hl : 4*(canonicalCompletedNativeLogDerivativeMoment 0:ℂ)*((n:ℂ)+1)+
      star (4*(canonicalCompletedNativeLogDerivativeMoment 0:ℂ)*((0:ℕ):ℂ)+
        4*(canonicalCompletedNativeLogDerivativeMoment 0:ℂ))-
      star (-1+(1:ℂ))*(4*(canonicalCompletedNativeLogDerivativeMoment 0:ℂ)*((n:ℂ)+1)) =
      4*(canonicalCompletedNativeLogDerivativeMoment 0:ℂ)*((n:ℂ)+2) := by
    simp
    ring
  simp only [Nat.cast_zero, zero_add, mul_one] at h
  have hl' : 4*(canonicalCompletedNativeLogDerivativeMoment 0:ℂ)*((n:ℂ)+1)+
      star (4*(canonicalCompletedNativeLogDerivativeMoment 0:ℂ))-
      star (-1+(1:ℂ))*(4*(canonicalCompletedNativeLogDerivativeMoment 0:ℂ)*((n:ℂ)+1)) =
      4*(canonicalCompletedNativeLogDerivativeMoment 0:ℂ)*((n:ℂ)+2) := by
    simpa only [Nat.cast_zero, mul_zero, zero_add] using hl
  rw [hl'] at h
  exact h.congr' (Eventually.of_forall (fun k => (he k).symm))

theorem incidentCoefficient_tangent (n : ℕ) :
    Tendsto (fun k => incidentCoefficient k n*radialScale k) atTop
      (nhds (4*(canonicalCompletedNativeLogDerivativeMoment 0:ℂ)*(n:ℂ))) := by
  have h := (feedbackDenominator_tangent n).const_mul ((n:ℂ)/((n:ℂ)+2))
  convert h using 1
  · funext k
    simp only [incidentCoefficient]
    ring
  · have hn : (n:ℂ)+2 ≠ 0 := by exact_mod_cast (show (n:ℝ)+2 ≠ 0 by positivity)
    field_simp

theorem central_deficit_tangent :
    Tendsto (fun k => oneDeficit k*((k:ℝ)+1)) atTop
      (nhds (8*canonicalCompletedNativeLogDerivativeMoment 0)) := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp (feedbackDenominator_tangent 0)
  have he (k : ℕ) : feedbackDenominator k 0 = (oneDeficit k:ℂ) := by
    change deficit (oneReturn k) = _
    exact native_deficit k
  convert h using 1 <;> norm_num [Function.comp_def, he, radialScale, Complex.mul_re]
  ring

/-- Every finite reduced source coordinate is legitimate eventually. This
does not require contractivity of the full finite native return. -/
theorem incidentCoefficient_eventually_ne_zero (n : ℕ) (hn : n ≠ 0) :
    ∀ᶠ k : ℕ in atTop, incidentCoefficient k n ≠ 0 := by
  have hm : (4:ℂ)*(canonicalCompletedNativeLogDerivativeMoment 0:ℂ)*(n:ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num)
      (by exact_mod_cast canonicalCompletedNativeLogDerivativeMoment_zero_pos.ne'))
      (by exact_mod_cast hn)
  have h := (incidentCoefficient_tangent n).eventually (eventually_ne_nhds hm)
  filter_upwards [h] with k hk
  exact (mul_ne_zero_iff.mp hk).1

theorem reduced_coordinates_eventually_valid (N : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ i : Fin N, incidentCoefficient k (i.val+1) ≠ 0 := by
  simpa only [Finset.mem_univ, forall_true_left] using
    (Finset.univ : Finset (Fin N)).eventually_all.2
      (fun i _ => incidentCoefficient_eventually_ne_zero (i.val+1) (by omega))

theorem reducedReturn_tendsto_one (n : ℕ) (hn : n ≠ 0) :
    Tendsto (fun k => reducedReturn k n) atTop (nhds 1) := by
  have hm : (4:ℂ)*(canonicalCompletedNativeLogDerivativeMoment 0:ℂ)*(n:ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num)
      (by exact_mod_cast canonicalCompletedNativeLogDerivativeMoment_zero_pos.ne'))
      (by exact_mod_cast hn)
  have h := (returnedCoefficient_tangent n).div (incidentCoefficient_tangent n) hm
  rw [div_self hm] at h
  apply h.congr'
  exact Eventually.of_forall (fun k => by
    change returnedCoefficient k n*radialScale k/(incidentCoefficient k n*radialScale k) =
      returnedCoefficient k n/incidentCoefficient k n
    exact mul_div_mul_right _ _ (radialScale_ne_zero k))

end
end CarryCauchyResidual
