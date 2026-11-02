import SigmaNeighborhood
import MomentosHankel.PivotLocalTransport

namespace CarryMovingSigma
open CarrySelfAdjointOperator CarrySigmaSource Matrix Filter Topology
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 10000000

def sigmaSchur (d : ℝ) (s n : ℕ) : ℝ :=
  sourceMomentSchur (completedSigmaLogJet d) s n

theorem sigma_schur_center (s n : ℕ) :
    sigmaSchur 0 s n = sourceMomentSchur canonicalCompletedNativeLogDerivativeMoment s n := by
  have hseq : completedSigmaLogJet 0 = canonicalCompletedNativeLogDerivativeMoment :=
    funext sigma_log_jet_center_eq_canonical
  simp only [sigmaSchur,hseq]

theorem central_schur_vector (s n : ℕ) :
    MomentosHankel.schurVector (sigmaMatrix 0 s n)
      (sourceMomentCoupling (completedSigmaLogJet 0) s n) = canonicalCriticalVector s n := by
  have hseq : completedSigmaLogJet 0 = canonicalCompletedNativeLogDerivativeMoment :=
    funext sigma_log_jet_center_eq_canonical
  rw [sigma_matrix_center,hseq]
  rfl

/-- The actual moving pivot of the completed source. Its only prefix hypothesis
is central invertibility. All local smoothness and operator derivatives are derived. -/
theorem moving_schur_curvature (s n : ℕ)
    (hA : IsUnit (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment s n)) :
    iteratedDeriv 2 (fun d => sigmaSchur d s n) 0 =
      canonicalCriticalVector s n ⬝ᵥ
        (sigmaMatrixSecond 0 s (n+1) *ᵥ canonicalCriticalVector s n) := by
  obtain ⟨U,hU,h0,hunit,hana⟩ := exists_sigma_prefix_neighborhood s n hA
  let A := fun d => sigmaMatrix d s n
  let b := fun d => sourceMomentCoupling (completedSigmaLogJet d) s n
  let c := fun d => completedSigmaLogJet d (2*n+s)
  let G := fun d => sigmaMatrix d s (n+1)
  let G₁ := fun d => sigmaMatrixFirst d s (n+1)
  let G₂ := fun d => sigmaMatrixSecond d s (n+1)
  have hAd : ∀ d ∈ U, DifferentiableAt ℝ A d := by
    intro d hd
    apply differentiableAt_pi.mpr
    intro i
    apply differentiableAt_pi.mpr
    intro j
    exact (hana d hd (i.val+j.val+s) (by omega)).differentiableAt
  have hbd : ∀ d ∈ U, DifferentiableAt ℝ b d := by
    intro d hd
    apply differentiableAt_pi.mpr
    intro i
    exact (hana d hd (i.val+n+s) (by omega)).differentiableAt
  have hG : ∀ d ∈ U,
      HasDerivAt (fun x => toEuclideanCLM (𝕜 := ℝ) (G x))
        (toEuclideanCLM (𝕜 := ℝ) (G₁ d)) d := by
    intro d hd
    apply sigma_matrix_operator_first
    intro i j
    exact hana d hd (i.val+j.val+s) (by omega)
  have hh := MomentosHankel.pivot_second_deriv_hankel_local A b c G G₁ G₂ 0 U hU h0
    (by intro d i j; rfl)
    (by intro d i; rfl)
    (by intro d j; simp [G,b,sigmaMatrix,sourceMomentMatrix,sourceMomentCoupling,Nat.add_comm])
    (by intro d; simp [G,c,sigmaMatrix,sourceMomentMatrix,two_mul])
    hunit hAd hbd hG (sigma_matrix_operator_second_center s (n+1))
    (fun d _ => sigma_matrix_symm d s (n+1)) (sigma_matrix_first_center s (n+1))
  change deriv (deriv (fun d => sigmaSchur d s n)) 0 = _ at hh
  have hv : MomentosHankel.schurVector (A 0) (b 0) = canonicalCriticalVector s n :=
    central_schur_vector s n
  rw [hv] at hh
  simpa only [iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero] using hh

/-- All ordered pairs of the same central critical vector, with the sector
in both the moment index and the curvature weight. No sign is claimed. -/
theorem moving_schur_curvature_expanded (s n : ℕ)
    (hA : IsUnit (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment s n)) :
    iteratedDeriv 2 (fun d => sigmaSchur d s n) 0 =
      -2 * ∑ i : Fin (n+1), ∑ j : Fin (n+1),
        canonicalCriticalVector s n i * canonicalCriticalVector s n j *
        (((i.val+j.val+s:ℕ):ℝ)+1)*(2*((i.val+j.val+s:ℕ):ℝ)+3)*
        canonicalCompletedNativeLogDerivativeMoment (i.val+j.val+s+1) := by
  rw [moving_schur_curvature s n hA]
  simp only [dotProduct,Matrix.mulVec,sigmaMatrixSecond,sigma_log_jet_curvature_center,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Closes the fixed-versus-moving obligation of PR139, for every sector/order
with invertible central prefix, using the identical canonical direction. -/
theorem moving_schur_eq_fixed_form_curvature (s n : ℕ)
    (hA : IsUnit (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment s n)) :
    iteratedDeriv 2 (fun d => sigmaSchur d s n) 0 =
      iteratedDeriv 2 (fun d => sigmaMomentForm d s (n+1) (canonicalCriticalVector s n)) 0 := by
  rw [moving_schur_curvature_expanded s n hA,sigma_critical_form_curvature_center]

end
end CarryMovingSigma
