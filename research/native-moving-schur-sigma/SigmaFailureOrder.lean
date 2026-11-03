import SigmaFirstHankelFailure
import MovingSchur
import CarrySelfAdjointOperator.NativeSourceAllOrderSchur

open scoped Matrix
open CarrySelfAdjointOperator CarrySigmaSource CarryMovingSigma CarryMomentLogConvex
  Filter Topology

namespace CarrySigmaObstruction
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- The original moving Schur pivot is continuous at the center whenever its
central prefix is positive definite. Its entries remain the original sigma jets. -/
theorem sigmaSchur_continuous_center_of_posDef (n : ℕ)
    (hA : (sigmaMatrix 0 0 n).PosDef) :
    ContinuousAt (fun d : ℝ => sigmaSchur d 0 n) 0 := by
  let A : ℝ → Matrix (Fin n) (Fin n) ℝ := fun d => sigmaMatrix d 0 n
  let b : ℝ → (Fin n → ℝ) := fun d =>
    sourceMomentCoupling (completedSigmaLogJet d) 0 n
  let c : ℝ → ℝ := fun d => completedSigmaLogJet d (2 * n)
  have hAcont : ContinuousAt A 0 := by
    simpa [A] using sigma_matrix_continuous_center 0 n
  have hbcont : ContinuousAt b 0 := by
    apply continuousAt_pi.mpr
    intro i
    exact (sigma_log_jet_analytic_center (i.val + n)).continuousAt
  have hccont : ContinuousAt c 0 := by
    exact (sigma_log_jet_analytic_center (2 * n)).continuousAt
  have hinv : ContinuousAt (fun d : ℝ => (A d)⁻¹) 0 := by
    have hdetcont : ContinuousAt (fun d : ℝ => (A d).det) 0 := by
      exact (continuous_id.matrix_det.continuousAt).comp hAcont
    have hdet0 : (A 0).det ≠ 0 := hA.det_pos.ne'
    have hinvdet : ContinuousAt (fun d : ℝ => ((A d).det)⁻¹) 0 :=
      hdetcont.inv₀ hdet0
    have hadj : ContinuousAt (fun d : ℝ => (A d).adjugate) 0 := by fun_prop
    have hformula : (fun d : ℝ => (A d)⁻¹) =
        (fun d : ℝ => ((A d).det)⁻¹ • (A d).adjugate) := by
      funext d
      rw [Matrix.inv_def, Ring.inverse_eq_inv]
    rw [hformula]
    exact hinvdet.smul hadj
  have hmul : ContinuousAt (fun d : ℝ => (A d)⁻¹ *ᵥ b d) 0 := by
    fun_prop
  have hdot : ContinuousAt (fun d : ℝ => b d ⬝ᵥ ((A d)⁻¹ *ᵥ b d)) 0 := by
    fun_prop
  have hformula : (fun d : ℝ => sigmaSchur d 0 n) =
      (fun d : ℝ => c d - b d ⬝ᵥ ((A d)⁻¹ *ᵥ b d)) := by
    funext d
    simp [sigmaSchur, A, b, c, sourceMomentSchur, sigmaMatrix]
  rw [hformula]
  exact hccont.sub hdot

/-- Positive definiteness passes from a finite moment matrix to every leading
principal prefix. -/
theorem sourceMomentMatrix_prefix_posDef (m : ℕ → ℝ) (s N k : ℕ)
    (hk : k ≤ N) (hN : (sourceMomentMatrix m s N).PosDef) :
    (sourceMomentMatrix m s k).PosDef := by
  have hsub := hN.submatrix (Fin.castLE_injective hk)
  have heq : (sourceMomentMatrix m s N).submatrix (Fin.castLE hk) (Fin.castLE hk) =
      sourceMomentMatrix m s k := by
    ext i j
    rfl
  rw [← heq]
  exact hsub

/-- A positive central prefix makes its moving Schur pivot positive for all
sufficiently small displacements. -/
theorem sigmaSchur_eventually_positive_of_center_prefix (n : ℕ)
    (hA : (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment 0 n).PosDef)
    (hp : 0 < sourceMomentSchur canonicalCompletedNativeLogDerivativeMoment 0 n) :
    ∀ᶠ d : ℝ in 𝓝 0, 0 < sigmaSchur d 0 n := by
  have hcont := sigmaSchur_continuous_center_of_posDef n (by
    simpa [sigma_matrix_center] using hA)
  have hp0 : 0 < sigmaSchur 0 0 n := by
    rwa [sigma_schur_center]
  exact hcont.eventually (Ioi_mem_nhds hp0)

/-- Every one of a finite list of central Schur pivots stays positive near zero
when the largest central prefix is positive definite. -/
theorem sigmaSchur_finite_eventually_positive (N : ℕ)
    (hN : (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment 0 N).PosDef) :
    ∀ᶠ d : ℝ in 𝓝 0, ∀ n < N, 0 < sigmaSchur d 0 n := by
  have hevent : ∀ i : Fin N, ∀ᶠ d : ℝ in 𝓝 0, 0 < sigmaSchur d 0 i := by
    intro i
    have hprev := sourceMomentMatrix_prefix_posDef
      canonicalCompletedNativeLogDerivativeMoment 0 N i (by omega) hN
    have hnext := sourceMomentMatrix_prefix_posDef
      canonicalCompletedNativeLogDerivativeMoment 0 N (i + 1) (by omega) hN
    have hp := (sourceMomentMatrix_succ_posDef_iff
      canonicalCompletedNativeLogDerivativeMoment 0 i hprev).mp hnext
    exact sigmaSchur_eventually_positive_of_center_prefix i hprev hp
  filter_upwards [Filter.eventually_all.mpr hevent] with d hd
  intro n hn
  exact hd ⟨n, hn⟩

/-- Positive Schur pivots build a positive definite source moment matrix by
successive exact extensions. -/
theorem sourceMomentMatrix_posDef_of_pivots (m : ℕ → ℝ) (N : ℕ)
    (hp : ∀ n < N, 0 < sourceMomentSchur m 0 n) :
    (sourceMomentMatrix m 0 N).PosDef := by
  induction N with
  | zero =>
      apply Matrix.PosDef.of_dotProduct_mulVec_pos (sourceMomentMatrix_isHermitian m 0 0)
      intro x hx
      exact (hx (Subsingleton.elim _ _)).elim
  | succ N ih =>
      have hprev := ih (fun n hn => hp n (by omega))
      exact (sourceMomentMatrix_succ_posDef_iff m 0 N hprev).mpr (hp N (by omega))

/-- For each fixed finite order, positive definiteness at the center persists
for the original moving sigma matrix near zero. -/
theorem sigmaMatrix_finite_eventually_posDef (N : ℕ)
    (hN : (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment 0 N).PosDef) :
    ∀ᶠ d : ℝ in 𝓝 0, (sigmaMatrix d 0 N).PosDef := by
  filter_upwards [sigmaSchur_finite_eventually_positive N hN] with d hd
  have h := sourceMomentMatrix_posDef_of_pivots (completedSigmaLogJet d) N hd
  simpa [sigmaMatrix] using h

/-- The least failing original sigma Hankel order selected from the established
positive-height-zero obstruction. Its hypotheses retain the original domain. -/
noncomputable def sigmaFirstFailureOrder (d γ : ℝ) (hγ : 0 < γ)
    (hd₀ : 0 < |d|) (hd₁ : |d| < (1 / 4 : ℝ))
    (hzero : completedNativeOperatorCharacteristic (γ : ℂ) = 0) : ℕ :=
  Classical.choose (exists_first_sigma_hankel_failure_of_zero d γ hγ hd₀ hd₁ hzero)

theorem sigmaFirstFailureOrder_spec (d γ : ℝ) (hγ : 0 < γ)
    (hd₀ : 0 < |d|) (hd₁ : |d| < (1 / 4 : ℝ))
    (hzero : completedNativeOperatorCharacteristic (γ : ℂ) = 0) :
    let N := sigmaFirstFailureOrder d γ hγ hd₀ hd₁ hzero
    0 < N ∧ ¬ (hankelMatrix (completedSigmaLogJet d) N).PosSemidef ∧
      ∀ m < N, (hankelMatrix (completedSigmaLogJet d) m).PosSemidef := by
  dsimp [sigmaFirstFailureOrder]
  obtain ⟨hNpos, hNbad, hNsmall, _⟩ := Classical.choose_spec
    (exists_first_sigma_hankel_failure_of_zero d γ hγ hd₀ hd₁ hzero)
  exact ⟨hNpos, hNbad, hNsmall⟩

/-- Under explicit all-order positive definiteness at the center, the least
failing order tends to infinity as a nonzero displacement tends to zero. For
every finite cutoff M, all orders through M remain positive definite nearby;
the established zero obstruction then forces the first failing order above M. -/
theorem sigmaFirstFailureOrder_tends_to_infty_of_center_posDef
    (γ : ℝ) (hγ : 0 < γ)
    (hzero : completedNativeOperatorCharacteristic (γ : ℂ) = 0)
    (hcentral : ∀ N : ℕ,
      (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment 0 N).PosDef) :
    ∀ M : ℕ, ∃ ε : ℝ, 0 < ε ∧
      ∀ d : ℝ, (hd₀ : 0 < |d|) → (hd₁ : |d| < (1 / 4 : ℝ)) → |d| < ε →
        M < sigmaFirstFailureOrder d γ hγ hd₀ hd₁ hzero := by
  intro M
  have hfinite := sigmaMatrix_finite_eventually_posDef M (hcentral M)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hfinite
  refine ⟨ε, hε, ?_⟩
  intro d hd₀ hd₁ hdε
  let h0 : 0 < |d| := hd₀
  let h1 : |d| < (1 / 4 : ℝ) := hd₁
  let N := sigmaFirstFailureOrder d γ hγ h0 h1 hzero
  have hspec := sigmaFirstFailureOrder_spec d γ hγ h0 h1 hzero
  by_contra hNM
  have hNM' : N ≤ M := by omega
  have hdist : dist d 0 < ε := by
    simpa [Real.dist_eq] using hdε
  have hpdM := hball hdist
  have hsourceM : (sourceMomentMatrix (completedSigmaLogJet d) 0 M).PosDef := by
    simpa [sigmaMatrix] using hpdM
  have hsourceN := sourceMomentMatrix_prefix_posDef
    (completedSigmaLogJet d) 0 M N hNM' hsourceM
  have hpdN : (sigmaMatrix d 0 N).PosDef := by
    simpa [sigmaMatrix] using hsourceN
  have hpsd : (hankelMatrix (completedSigmaLogJet d) N).PosSemidef := by
    have hsource := hpdN.posSemidef
    simpa [completedSigmaLogJet_sigmaMatrix_eq_hankel] using hsource
  exact hspec.2.1 hpsd

#print axioms sigmaSchur_continuous_center_of_posDef
#print axioms sourceMomentMatrix_prefix_posDef
#print axioms sigmaSchur_eventually_positive_of_center_prefix
#print axioms sigmaSchur_finite_eventually_positive
#print axioms sourceMomentMatrix_posDef_of_pivots
#print axioms sigmaMatrix_finite_eventually_posDef
#print axioms sigmaFirstFailureOrder_spec
#print axioms sigmaFirstFailureOrder_tends_to_infty_of_center_posDef

end
end CarrySigmaObstruction
