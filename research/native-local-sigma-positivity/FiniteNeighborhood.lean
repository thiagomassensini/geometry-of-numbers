import LocalPositivity
import OddTrialPositivity

namespace CarryLocalPositivity
open CarrySelfAdjointOperator CarrySigmaSource CarryMovingSigma Matrix Filter Topology
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 10000000

theorem sourceMomentMatrix_prefix_posDef (m : ℕ → ℝ) (s N k : ℕ)
    (hk : k ≤ N) (h : (sourceMomentMatrix m s N).PosDef) :
    (sourceMomentMatrix m s k).PosDef := by
  have ht := h.submatrix (Fin.castLE_injective hk)
  have he : (sourceMomentMatrix m s N).submatrix (Fin.castLE hk) (Fin.castLE hk) =
      sourceMomentMatrix m s k := by
    ext i j
    rfl
  rw [← he]
  exact ht

theorem sigmaSchur_eventually_positive (s n : ℕ)
    (hA : IsUnit (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment s n))
    (hp : 0 < sourceMomentSchur canonicalCompletedNativeLogDerivativeMoment s n) :
    ∀ᶠ d : ℝ in 𝓝 0, 0 < sigmaSchur d s n := by
  have hc := (sigmaSchur_differentiable_center s n hA).continuousAt
  have hp0 : 0 < sigmaSchur 0 s n := by rwa [sigma_schur_center]
  exact hc (isOpen_Ioi.mem_nhds hp0)

theorem sigmaSchur_finite_eventually_positive (s N : ℕ)
    (hpos : (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment s N).PosDef) :
    ∀ᶠ d : ℝ in 𝓝 0, ∀ n < N, 0 < sigmaSchur d s n := by
  have h : ∀ i : Fin N, ∀ᶠ d : ℝ in 𝓝 0, 0 < sigmaSchur d s i := by
    intro i
    have hprev := sourceMomentMatrix_prefix_posDef canonicalCompletedNativeLogDerivativeMoment s N i (by omega) hpos
    have hnext := sourceMomentMatrix_prefix_posDef canonicalCompletedNativeLogDerivativeMoment s N (i+1) (by omega) hpos
    have hp := (sourceMomentMatrix_succ_posDef_iff canonicalCompletedNativeLogDerivativeMoment s i hprev).mp hnext
    exact sigmaSchur_eventually_positive s i hprev.isUnit hp
  filter_upwards [Filter.eventually_all.mpr h] with d hd
  intro n hn
  exact hd ⟨n,hn⟩

theorem sourceMomentMatrix_posDef_of_pivots (m : ℕ → ℝ) (s N : ℕ)
    (hp : ∀ n < N, 0 < sourceMomentSchur m s n) :
    (sourceMomentMatrix m s N).PosDef := by
  induction N with
  | zero =>
    apply Matrix.PosDef.of_dotProduct_mulVec_pos (sourceMomentMatrix_isHermitian _ _ _)
    intro x hx
    exact (hx (Subsingleton.elim _ _)).elim
  | succ N ih =>
    have hprev := ih (fun n hn => hp n (by omega))
    apply (sourceMomentMatrix_succ_posDef_iff m s N hprev).mpr
    exact hp N (by omega)

theorem sigmaMatrix_finite_eventually_posDef (s N : ℕ)
    (hpos : (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment s N).PosDef) :
    ∀ᶠ d : ℝ in 𝓝 0, (sigmaMatrix d s N).PosDef := by
  filter_upwards [sigmaSchur_finite_eventually_positive s N hpos] with d hd
  exact sourceMomentMatrix_posDef_of_pivots (completedSigmaLogJet d) s N hd

theorem both_six_sigmaMatrices_eventually_posDef :
    ∀ᶠ d : ℝ in 𝓝 0, (sigmaMatrix d 0 6).PosDef ∧ (sigmaMatrix d 1 6).PosDef := by
  have he : (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment 0 6).PosDef := by
    exact CarrySixthEven.even_source_six_posDef
  have ho : (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment 1 6).PosDef := by
    exact CarrySixthOdd.odd_source_six_posDef
  exact (sigmaMatrix_finite_eventually_posDef 0 6 he).and (sigmaMatrix_finite_eventually_posDef 1 6 ho)

/-- Some noncentral displacements retain both finite positive matrices.
No explicit numerical radius or all-order positivity is claimed. -/
theorem exists_positive_noncentral_six_sections :
    ∃ d : ℝ, 0 < d ∧ d < 1/2 ∧ (sigmaMatrix d 0 6).PosDef ∧ (sigmaMatrix d 1 6).PosDef := by
  obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff.mp both_six_sigmaMatrices_eventually_posDef
  let d : ℝ := min ε (1/2) / 2
  have hm : 0 < min ε (1/2:ℝ) := lt_min hε (by norm_num)
  have hd : 0 < d := by dsimp [d]; linarith
  have hdhalf : d < 1/2 := by
    have hh := min_le_right ε (1/2:ℝ)
    dsimp [d]
    linarith
  have hdε : d < ε := by
    have hh := min_le_left ε (1/2:ℝ)
    dsimp [d]
    linarith
  refine ⟨d,hd,hdhalf,?_⟩
  apply hball
  simpa [Real.dist_eq,abs_of_pos hd] using hdε

#print axioms exists_positive_noncentral_six_sections

#print axioms sigmaSchur_finite_eventually_positive
#print axioms sigmaMatrix_finite_eventually_posDef
#print axioms both_six_sigmaMatrices_eventually_posDef
end
end CarryLocalPositivity
