import ForcingSlope
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! Strong regularity of the ORIGINAL completed material state. The proof
uses the pre-existing locally uniformly convergent complex gradient series,
then packs its interior and actual whole-cell return in the SAME Hilbert
product. It makes no claim about powers of an unbounded clock. -/
namespace CarryNativePhase
open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.BaseTwoCompletion
open CarryForcingResidual CarryMixedGreen
open scoped InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem material_gradient_analytic (t : ℝ) :
    AnalyticAt ℝ baseTwoCompletedMaterialGradientL2 t := by
  have hC : AnalyticAt ℂ (baseTwoComplexMaterialGradientLp 2) (t:ℂ) :=
    (baseTwoComplexMaterialGradientLp_differentiableOn_ball 2 t).analyticAt
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num)))
  have hR := (hC.restrictScalars (𝕜 := ℝ)).comp (Complex.ofRealCLM.analyticAt t)
  have he : baseTwoComplexMaterialGradientLp 2 ∘ Complex.ofReal =
      baseTwoCompletedMaterialGradientL2 := by
    funext u
    exact baseTwoComplexMaterialGradientLp_ofReal 2 (by norm_num) u _ (fun _ => rfl)
  simpa only [Complex.ofRealCLM_apply, he] using hR

theorem material_boundary_analytic (t : ℝ) :
    AnalyticAt ℝ baseTwoCompletedBoundaryValue t := by
  have he : baseTwoCompletedBoundaryValue = fun u => baseTwoCriticalCompleteSignal u - 1 := by
    funext u
    have h := baseTwoCompletedBoundaryValue_add_seed_eq_signal u
    simpa only [criticalMaterialSample_one, eq_sub_iff_add_eq, add_comm] using h
  rw [he]
  exact (baseTwoCriticalCompleteSignal_analyticAt t).sub analyticAt_const

/-- Full vector result BEFORE any scalar probe or Green observation. -/
theorem material_state_analytic (t : ℝ) :
    AnalyticAt ℝ baseTwoCompletedBoundaryHilbertState t := by
  let innerPack := (WithLp.prodContinuousLinearEquiv 2 ℂ MaterialEdgeL2 ℂ).symm
  have hi := ((innerPack.toContinuousLinearMap.restrictScalars ℝ).analyticAt _).comp
    ((material_gradient_analytic t).prod (material_boundary_analytic t))
  let outerPack := (WithLp.prodContinuousLinearEquiv 2 ℂ ℂ (WithLp 2 (MaterialEdgeL2 × ℂ))).symm
  have ho := ((outerPack.toContinuousLinearMap.restrictScalars ℝ).analyticAt _).comp
    ((analyticAt_const (v := (1:ℂ))).prod hi)
  convert ho using 1
  funext u
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · exact criticalMaterialSample_one u
  · rfl

def sourceCenter (t : ℝ) : ℂ :=
  carryMaterialClockCentralCoefficient (baseTwoCompletedBoundaryHilbertState t)

def sourceOverlap (t : ℝ) : ℂ :=
  inner ℂ carryMaterialClockCentralForcing (carryMaterialClockComplementState t)

theorem source_center_analytic (t : ℝ) : AnalyticAt ℝ sourceCenter t :=
  ((carryMaterialClockCentralCoefficient.restrictScalars ℝ).analyticAt _).comp (material_state_analytic t)

theorem source_overlap_analytic (t : ℝ) : AnalyticAt ℝ sourceOverlap t :=
  ((((innerSL ℂ carryMaterialClockCentralForcing).comp carryMaterialCentralComplement).restrictScalars ℝ).analyticAt _).comp
    (material_state_analytic t)

theorem source_center_origin : sourceCenter 0 = 1 := carryMaterialClock_central_coefficient_zero
theorem source_overlap_origin : sourceOverlap 0 = 0 := by
  simp [sourceOverlap, carryMaterialClock_complement_origin]

theorem source_overlap_derivative :
    HasDerivAt sourceOverlap (-Complex.I*((‖carryMaterialClockCentralForcing‖^2:ℝ):ℂ)) 0 := by
  have h := ((innerSL ℂ carryMaterialClockCentralForcing).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    carryMaterialClock_complement_origin_derivative
  change HasDerivAt sourceOverlap
    (inner ℂ carryMaterialClockCentralForcing (-Complex.I • carryMaterialClockCentralForcing)) 0 at h
  have hw : inner ℂ carryMaterialClockCentralForcing carryMaterialClockCentralForcing =
      ((‖carryMaterialClockCentralForcing‖^2:ℝ):ℂ) := by
    apply Complex.ext
    · exact material_inner_self_re _
    · exact inner_self_im (𝕜 := ℂ) carryMaterialClockCentralForcing
  simpa only [inner_smul_right, hw] using h

theorem native_ratio_analytic : AnalyticAt ℝ valueRatio 0 := by
  have h := ((analyticAt_const (v := (2*Complex.I))).mul (source_overlap_analytic 0)).div
    (source_center_analytic 0) (by rw [source_center_origin]; exact one_ne_zero)
  apply h.congr
  have hn := (source_center_analytic 0).continuousAt.eventually_ne
    (show sourceCenter 0 ≠ 0 by rw [source_center_origin]; exact one_ne_zero)
  filter_upwards [hn] with t ht
  exact (value_ratio_undressed t ht).symm

theorem forcing_scalar_analytic (t : ℝ) : AnalyticAt ℝ carryMaterialClockForcingScalar t :=
  (analyticAt_const.mul (baseTwoCanonicalDressingScalar_analyticAt t)).mul (source_center_analytic t)

theorem dressed_state_analytic (t : ℝ) :
    AnalyticAt ℝ (fun u => baseTwoVectorDressing u (baseTwoCompletedBoundaryHilbertState u)) t := by
  have h := (baseTwoCanonicalDressingScalar_analyticAt t).smul (material_state_analytic t)
  change AnalyticAt ℝ
    (fun u => baseTwoCanonicalDressingScalar u • baseTwoCompletedBoundaryHilbertState u) t at h
  simpa only [baseTwoVectorDressing_apply] using h

theorem companion_first_analytic (t : ℝ) :
    AnalyticAt ℝ (fun u => (carryMaterialCompanionValuePair u).1) t := by
  have he : (fun u => (carryMaterialCompanionValuePair u).1) =
      fun u => -deriv (fun v => baseTwoVectorDressing v (baseTwoCompletedBoundaryHilbertState v)) u := by
    funext u
    have hd := (carryMaterialDressedSource_hasDerivAt u).deriv
    change (carryMaterialCompanionValuePair u).1 = -deriv _ u
    rw [hd, neg_neg]
    rfl
  rw [he]
  exact (dressed_state_analytic t).deriv.neg

theorem compressed_first_analytic (t : ℝ) :
    AnalyticAt ℝ (fun u => (carryMaterialClockCompressedPair u).1) t := by
  have he : (fun u => (carryMaterialClockCompressedPair u).1) = fun u =>
      carryMaterialCentralComplement (carryMaterialCompanionValuePair u).1 -
        carryMaterialClockForcingScalar u • carryMaterialClockCentralForcing := by
    funext u
    have hh := congrArg Prod.fst (carryMaterialClock_companion_complement u)
    change carryMaterialCentralComplement (carryMaterialCompanionValuePair u).1 =
      (carryMaterialClockCompressedPair u).1 +
        carryMaterialClockForcingScalar u • carryMaterialClockCentralForcing at hh
    rw [hh, add_sub_cancel_right]
  rw [he]
  exact (((carryMaterialCentralComplement.restrictScalars ℝ).analyticAt _).comp
    (companion_first_analytic t)).sub ((forcing_scalar_analytic t).smul analyticAt_const)

theorem companion_probe_analytic (t : ℝ) : AnalyticAt ℝ companionProbe t :=
  (((innerSL ℂ carryMaterialClockCentralForcing).restrictScalars ℝ).analyticAt _).comp
    (compressed_first_analytic t)

end
end CarryNativePhase
