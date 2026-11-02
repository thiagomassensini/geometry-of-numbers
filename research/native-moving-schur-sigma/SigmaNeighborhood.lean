import SigmaQuadratic
import MatrixJetCalculus

namespace CarryMovingSigma
open CarrySelfAdjointOperator CarrySigmaSource Matrix Filter Topology
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000

def sigmaMatrix (d : ℝ) (s N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  sourceMomentMatrix (completedSigmaLogJet d) s N

def sigmaMatrixFirst (d : ℝ) (s N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => deriv (fun x => completedSigmaLogJet x (i.val+j.val+s)) d

def sigmaMatrixSecond (d : ℝ) (s N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => iteratedDeriv 2 (fun x => completedSigmaLogJet x (i.val+j.val+s)) d

theorem sigma_matrix_center (s N : ℕ) :
    sigmaMatrix 0 s N = sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment s N := by
  ext i j
  exact sigma_log_jet_center_eq_canonical _

theorem sigma_matrix_continuous_center (s N : ℕ) :
    ContinuousAt (fun d => sigmaMatrix d s N) 0 := by
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro j
  exact (sigma_log_jet_analytic_center _).continuousAt

theorem sigma_matrix_first_center (s N : ℕ) : sigmaMatrixFirst 0 s N = 0 := by
  ext i j
  exact sigma_log_jet_deriv_center _

theorem sigma_matrix_symm (d : ℝ) (s N : ℕ) : (sigmaMatrix d s N).IsSymm := by
  ext i j
  simp [sigmaMatrix,sourceMomentMatrix,Nat.add_comm]

/-- A single open neighborhood supplies all finitely many analytic moment jets
and an invertible original prefix, derived only from its central invertibility. -/
theorem exists_sigma_prefix_neighborhood (s n : ℕ)
    (hA : IsUnit (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment s n)) :
    ∃ U : Set ℝ, IsOpen U ∧ (0:ℝ) ∈ U ∧
      (∀ d ∈ U, IsUnit (sigmaMatrix d s n)) ∧
      (∀ d ∈ U, ∀ k < 2*n+s+1, AnalyticAt ℝ (fun x => completedSigmaLogJet x k) d) := by
  have hs : ∀ᶠ d : ℝ in 𝓝 0, ∀ k : Fin (2*n+s+1),
      AnalyticAt ℝ (fun x => completedSigmaLogJet x k.val) d :=
    Filter.eventually_all.mpr (fun k => (sigma_log_jet_analytic_center k.val).eventually_analyticAt)
  have hcont := sigma_matrix_continuous_center s n
  have hdetcont : ContinuousAt (fun d => (sigmaMatrix d s n).det) 0 :=
    (continuous_id.matrix_det.continuousAt).comp hcont
  have hdet0 : (sigmaMatrix 0 s n).det ≠ 0 := by
    rw [sigma_matrix_center]
    exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hA)
  have hdet := hdetcont.eventually_ne hdet0
  obtain ⟨U,hsub,hU,h0⟩ := eventually_nhds_iff.mp (hdet.and hs)
  refine ⟨U,hU,h0,?_,?_⟩
  · intro d hd
    exact (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (hsub d hd).1)
  · intro d hd k hk
    exact (hsub d hd).2 ⟨k,hk⟩

theorem sigma_matrix_operator_first (s N : ℕ) (d : ℝ)
    (ha : ∀ i j : Fin N, AnalyticAt ℝ (fun x => completedSigmaLogJet x (i.val+j.val+s)) d) :
    HasDerivAt (fun x => toEuclideanCLM (𝕜 := ℝ) (sigmaMatrix x s N))
      (toEuclideanCLM (𝕜 := ℝ) (sigmaMatrixFirst d s N)) d := by
  exact euclideanCLM_hasDerivAt_of_entries _ _ d (fun i j => (ha i j).differentiableAt.hasDerivAt)

theorem sigma_matrix_operator_second_center (s N : ℕ) :
    HasDerivAt (fun x => toEuclideanCLM (𝕜 := ℝ) (sigmaMatrixFirst x s N))
      (toEuclideanCLM (𝕜 := ℝ) (sigmaMatrixSecond 0 s N)) 0 := by
  apply euclideanCLM_hasDerivAt_of_entries
  intro i j
  have ha := sigma_log_jet_analytic_center (i.val+j.val+s)
  simpa only [sigmaMatrixFirst,sigmaMatrixSecond,iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero]
    using ha.deriv.differentiableAt.hasDerivAt

end
end CarryMovingSigma
