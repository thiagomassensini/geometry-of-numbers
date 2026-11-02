import SourceSignRegression
import Mathlib.Analysis.Calculus.DerivativeTest

namespace CarryLocalPositivity
open CarrySelfAdjointOperator CarrySigmaSource CarryMovingSigma CarryCriticalEuler Matrix Filter Topology
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 10000000

theorem sigmaSchur_even (s n : ℕ) (d : ℝ) (hd₁ : -(1/2:ℝ)<d) (hd₂ : d<(1/2:ℝ)) :
    sigmaSchur (-d) s n = sigmaSchur d s n := by
  have he : completedSigmaLogJet (-d) = completedSigmaLogJet d := by
    funext k
    exact sigma_log_jet_even d hd₁ hd₂ k
  simp only [sigmaSchur, he]

theorem sigmaSchur_differentiable_center (s n : ℕ)
    (hA : IsUnit (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment s n)) :
    DifferentiableAt ℝ (fun d => sigmaSchur d s n) 0 := by
  let A := fun d => sigmaMatrix d s n
  let b := fun d => sourceMomentCoupling (completedSigmaLogJet d) s n
  have hAd : DifferentiableAt ℝ A 0 := by
    apply differentiableAt_pi.mpr
    intro i
    apply differentiableAt_pi.mpr
    intro j
    exact (sigma_log_jet_analytic_center (i.val+j.val+s)).differentiableAt
  have hbd : DifferentiableAt ℝ b 0 := by
    apply differentiableAt_pi.mpr
    intro i
    exact (sigma_log_jet_analytic_center (i.val+n+s)).differentiableAt
  have hAu : IsUnit (A 0) := by simpa [A,sigma_matrix_center] using hA
  have hInv := MomentosHankel.matrixInverse_differentiableAt A 0 hAd hAu
  have hv := MomentosHankel.mulVec_differentiableAt (fun d => (A d)⁻¹) b 0 hInv hbd
  have hsum : DifferentiableAt ℝ (fun d => b d ⬝ᵥ ((A d)⁻¹ *ᵥ b d)) 0 := by
    unfold dotProduct
    have he : (fun d => ∑ i : Fin n, b d i * ((A d)⁻¹ *ᵥ b d) i) =
        (∑ i : Fin n, fun d => b d i * ((A d)⁻¹ *ᵥ b d) i) := by
      funext d
      simp only [Finset.sum_apply]
    rw [he]
    apply DifferentiableAt.sum
    intro i hi
    exact ((differentiableAt_pi.mp hbd) i).mul ((differentiableAt_pi.mp hv) i)
  have hc := (sigma_log_jet_analytic_center (2*n+s)).differentiableAt
  exact hc.sub hsum

theorem sigmaSchur_deriv_center (s n : ℕ)
    (hA : IsUnit (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment s n)) :
    deriv (fun d => sigmaSchur d s n) 0 = 0 := by
  let g : ℝ → ℝ := fun d => sigmaSchur d s n
  have hg : HasDerivAt g (deriv g 0) 0 := (sigmaSchur_differentiable_center s n hA).hasDerivAt
  have hminus : HasDerivAt (fun d : ℝ => -d) (-1) 0 := by
    simpa only [id_eq,zero_sub] using (hasDerivAt_id (0:ℝ)).const_sub 0
  have hn : HasDerivAt (fun d : ℝ => g (-d)) (-(deriv g 0)) 0 := by
    have h := HasDerivAt.comp (0:ℝ)
      (show HasDerivAt g (deriv g 0) (-0) by simpa only [neg_zero] using hg) hminus
    simpa only [Function.comp_def,neg_one_mul,mul_neg_one] using h
  have he : (fun d : ℝ => g (-d)) =ᶠ[𝓝 (0:ℝ)] g := by
    have hm : Set.Ioo (-(1/2:ℝ)) (1/2:ℝ) ∈ 𝓝 (0:ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
    filter_upwards [hm] with d hd
    exact sigmaSchur_even s n d hd.1 hd.2
  have hh := hg.unique (hn.congr_of_eventuallyEq he.symm)
  change deriv g 0 = 0
  linarith

theorem sigmaSchur_localMax_of_negative_curvature (s n : ℕ)
    (hA : IsUnit (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment s n))
    (hcurv : iteratedDeriv 2 (fun d => sigmaSchur d s n) 0 < 0) :
    IsLocalMax (fun d => sigmaSchur d s n) 0 := by
  apply isLocalMax_of_deriv_deriv_neg
  · simpa only [iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero] using hcurv
  · exact sigmaSchur_deriv_center s n hA
  · exact (sigmaSchur_differentiable_center s n hA).continuousAt

theorem second_even_localMax : IsLocalMax (fun d => sigmaSchur d 0 1) 0 :=
  sigmaSchur_localMax_of_negative_curvature 0 1 first_even_prefix_unit second_even_sigma_curvature_negative

theorem second_even_center_positive : 0 < sigmaSchur 0 0 1 := by
  rw [sigma_schur_center]
  rw [← NativeMomentOrthogonalization.sourceMomentSchur_critical_direction_of_isUnit
    canonicalCompletedNativeLogDerivativeMoment 0 1 first_even_prefix_unit]
  change 0 < sourceMomentQuadratic canonicalCompletedNativeLogDerivativeMoment 0 2 (canonicalCriticalVector 0 1)
  rw [second_even_critical_vector]
  let h := canonicalCompletedNativeLogDerivativeMoment
  have h0 : 0 < h 0 := canonicalCompletedNativeLogDerivativeMoment_zero_pos
  have hm := CarryCriticalMixed.source_nonlinear_margin_pos
  change 0 < h 0 * h 2 - 2 * (h 1)^2 at hm
  have h0ne : h 0 ≠ 0 := ne_of_gt h0
  have he : h 0 * sourceMomentQuadratic h 0 2 ![-h 1 / h 0, 1] =
      h 0 * h 2 - (h 1)^2 := by
    simp [sourceMomentQuadratic,sourceMomentMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
    field_simp [h0ne]
    ring
  change 0 < sourceMomentQuadratic h 0 2 ![-h 1 / h 0, 1]
  nlinarith [sq_nonneg (h 1)]

theorem second_even_eventually_positive :
    ∀ᶠ d : ℝ in 𝓝 0, 0 < sigmaSchur d 0 1 := by
  have hc := (sigmaSchur_differentiable_center 0 1 first_even_prefix_unit).continuousAt
  exact hc (isOpen_Ioi.mem_nhds second_even_center_positive)

theorem second_even_positive_local_max :
    IsLocalMax (fun d => sigmaSchur d 0 1) 0 ∧
      ∀ᶠ d : ℝ in 𝓝 0, 0 < sigmaSchur d 0 1 :=
  ⟨second_even_localMax,second_even_eventually_positive⟩

#print axioms second_even_center_positive
#print axioms second_even_eventually_positive
#print axioms second_even_positive_local_max

#print axioms sigmaSchur_even
#print axioms sigmaSchur_differentiable_center
#print axioms sigmaSchur_deriv_center
#print axioms second_even_localMax
end
end CarryLocalPositivity
