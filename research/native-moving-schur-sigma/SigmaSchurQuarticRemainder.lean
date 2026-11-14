import SigmaTransverseJoint
import MovingSchur
import LocalPositivity
import SchurLogic
import Mathlib.Analysis.Calculus.Taylor

/-!
# Fixed critical direction and quartic transverse control for the original sigma Schur pivot

The moving pivot is kept as `sigmaSchur`.  The fixed vector is the canonical center vector from
`SigmaQuadratic`; the correction term below retains the complete reacoupling with the old prefix.
-/
namespace CarryMovingSigma
open CarrySelfAdjointOperator CarrySigmaSource CarrySigmaObstruction CarryLocalPositivity
  NativeMomentOrthogonalization Matrix Filter Topology
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000

def sigmaCenterOldSolution (s n : ℕ) : Fin n → ℝ :=
  -((sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment s n)⁻¹ *ᵥ
    sourceMomentCoupling canonicalCompletedNativeLogDerivativeMoment s n)

def sigmaFixedCriticalDirection (s n : ℕ) : Fin (n+1) → ℝ :=
  canonicalCriticalVector s n

theorem sigmaFixedCriticalDirection_eq_original (s n : ℕ) :
    sigmaFixedCriticalDirection s n = canonicalCriticalVector s n := rfl

def sigmaReacoupledOldDirection (d : ℝ) (s n : ℕ) : Fin n → ℝ :=
  sigmaCenterOldSolution s n +
    (sigmaMatrix d s n)⁻¹ *ᵥ sourceMomentCoupling (completedSigmaLogJet d) s n

def sigmaFixedCriticalForm (d : ℝ) (s n : ℕ) : ℝ :=
  sourceMomentQuadratic (completedSigmaLogJet d) s (n+1) (sigmaFixedCriticalDirection s n)

def sigmaResidualCoupling (d : ℝ) (s n : ℕ) : Fin n → ℝ :=
  sigmaMatrix d s n *ᵥ sigmaCenterOldSolution s n +
    sourceMomentCoupling (completedSigmaLogJet d) s n

def sigmaReacouplingCorrection (d : ℝ) (s n : ℕ) : ℝ :=
  sourceMomentQuadratic (completedSigmaLogJet d) s n (sigmaReacoupledOldDirection d s n)

def sigmaSchurCurvatureAmplitude (s n : ℕ) : ℝ :=
  ∑ i : Fin (n+1), ∑ j : Fin (n+1),
    canonicalCriticalVector s n i * canonicalCriticalVector s n j *
      (((i.val+j.val+s:ℕ):ℝ)+1) *
        (2*((i.val+j.val+s:ℕ):ℝ)+3) *
        canonicalCompletedNativeLogDerivativeMoment (i.val+j.val+s+1)

/-- The exact Schur sewing identity at a fixed central critical direction.  The full
reacoupling term contains every old/new cross term. -/
theorem sigmaSchur_fixed_direction_exact (s n : ℕ) (d : ℝ)
    (hA : IsUnit (sigmaMatrix d s n)) :
    sigmaSchur d s n = sigmaFixedCriticalForm d s n - sigmaReacouplingCorrection d s n := by
  have h := sourceMomentSchur_sewing_of_isUnit (completedSigmaLogJet d) s n
    (by simpa [sigmaMatrix] using hA) (sigmaCenterOldSolution s n) 1
  have h' := h
  simp only [one_smul, one_pow, mul_one] at h'
  have h'' : sourceMomentSchur (completedSigmaLogJet d) s n =
      sourceMomentQuadratic (completedSigmaLogJet d) s (n+1)
        (Fin.snoc (sigmaCenterOldSolution s n) 1) -
      sourceMomentQuadratic (completedSigmaLogJet d) s n
        (sigmaCenterOldSolution s n + (sourceMomentMatrix (completedSigmaLogJet d) s n)⁻¹ *ᵥ
          sourceMomentCoupling (completedSigmaLogJet d) s n) := by
    linarith [h']
  change sourceMomentSchur (completedSigmaLogJet d) s n =
    sourceMomentQuadratic (completedSigmaLogJet d) s (n+1)
      (Fin.snoc (sigmaCenterOldSolution s n) 1) -
    sourceMomentQuadratic (completedSigmaLogJet d) s n
      (sigmaCenterOldSolution s n + (sourceMomentMatrix (completedSigmaLogJet d) s n)⁻¹ *ᵥ
        sourceMomentCoupling (completedSigmaLogJet d) s n)
  exact h''

/-- The residual coupling is the prefix matrix applied to the exact reacoupled direction. -/
theorem sigmaResidualCoupling_eq_matrix_mul_reacoupled (s n : ℕ) (d : ℝ)
    (hA : IsUnit (sigmaMatrix d s n)) :
    sigmaResidualCoupling d s n =
      sigmaMatrix d s n *ᵥ sigmaReacoupledOldDirection d s n := by
  let A := sigmaMatrix d s n
  letI := hA.invertible
  ext i
  simp only [sigmaResidualCoupling, sigmaReacoupledOldDirection, Matrix.mulVec_add,
    Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]

/-- The correction is exactly the residual-coupling inverse quadratic from the fixed-vector
identity in the mission statement. -/
theorem sigmaSchur_fixed_direction_residual_form (s n : ℕ) (d : ℝ)
    (hA : IsUnit (sigmaMatrix d s n)) :
    sigmaSchur d s n = sigmaFixedCriticalForm d s n -
      sigmaResidualCoupling d s n ⬝ᵥ
        ((sigmaMatrix d s n)⁻¹ *ᵥ sigmaResidualCoupling d s n) := by
  rw [sigmaSchur_fixed_direction_exact s n d hA]
  have hr := sigmaResidualCoupling_eq_matrix_mul_reacoupled s n d hA
  let A := sigmaMatrix d s n
  let r := sigmaReacoupledOldDirection d s n
  letI := hA.invertible
  have hinv : A⁻¹ *ᵥ sigmaResidualCoupling d s n = r := by
    calc
      A⁻¹ *ᵥ sigmaResidualCoupling d s n = A⁻¹ *ᵥ (A *ᵥ r) := by rw [hr]
      _ = (A⁻¹ * A) *ᵥ r := by rw [Matrix.mulVec_mulVec]
      _ = r := by rw [Matrix.inv_mul_of_invertible, Matrix.one_mulVec]
  have heq : sigmaResidualCoupling d s n ⬝ᵥ
      (A⁻¹ *ᵥ sigmaResidualCoupling d s n) =
      r ⬝ᵥ (A *ᵥ r) := by
    calc
      sigmaResidualCoupling d s n ⬝ᵥ
          (A⁻¹ *ᵥ sigmaResidualCoupling d s n) =
        (A *ᵥ r) ⬝ᵥ (A⁻¹ *ᵥ sigmaResidualCoupling d s n) := by rw [hr]
      _ = (A *ᵥ r) ⬝ᵥ r := by rw [hinv]
      _ = r ⬝ᵥ (A *ᵥ r) := dotProduct_comm _ _
  have hq : sigmaReacouplingCorrection d s n = r ⬝ᵥ (A *ᵥ r) := by
    simp [sigmaReacouplingCorrection, sourceMomentQuadratic, A, r, sigmaMatrix]
  rw [hq]
  linarith [heq]

/-- If the original prefix remains positive definite, the reacoupling correction is
nonnegative, so the moving pivot lies below the fixed-direction form. -/
theorem sigmaSchur_le_fixed_direction_of_posDef (s n : ℕ) (d : ℝ)
    (hA : IsUnit (sigmaMatrix d s n)) (hPos : (sigmaMatrix d s n).PosDef) :
    sigmaSchur d s n ≤ sigmaFixedCriticalForm d s n := by
  rw [sigmaSchur_fixed_direction_exact s n d hA]
  have hnonneg := hPos.posSemidef.dotProduct_mulVec_nonneg
    (sigmaReacoupledOldDirection d s n)
  change 0 ≤ sigmaReacouplingCorrection d s n at hnonneg
  linarith

private theorem matrixDet_analyticAt_of_entries {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ℝ → Matrix ι ι ℝ) (d : ℝ)
    (hentry : ∀ i j, AnalyticAt ℝ (fun x => A x i j) d) :
    AnalyticAt ℝ (fun x => (A x).det) d := by
  classical
  have hformula : (fun x : ℝ => (A x).det) =
      (fun x => ∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ * ∏ i, A x (σ i) i) := by
    funext x
    exact Matrix.det_apply' (A x)
  rw [hformula]
  have hsum : (fun x : ℝ =>
      ∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ * ∏ i, A x (σ i) i) =
      ∑ σ : Equiv.Perm ι, (fun x => Equiv.Perm.sign σ * ∏ i, A x (σ i) i) := by
    funext x
    simp
  rw [hsum]
  refine Finset.analyticAt_sum (Finset.univ : Finset (Equiv.Perm ι)) ?_
  intro σ hσ
  have hprod : AnalyticAt ℝ (fun x : ℝ => ∏ i : ι, A x (σ i) i) d := by
    have heq : (fun x : ℝ => ∏ i : ι, A x (σ i) i) =
        ∏ i : ι, (fun x => A x (σ i) i) := by
      funext x
      simp
    rw [heq]
    refine Finset.analyticAt_prod (𝕜 := ℝ) (A := ℝ) (Finset.univ : Finset ι) ?_
    intro i hi
    exact hentry (σ i) i
  exact analyticAt_const.mul hprod

/-- The moving pivot is analytic at every point where the original prefix is invertible
and all source jets entering the bordered matrix are analytic. -/
theorem sigmaSchur_analyticAt_of_prefix (s n : ℕ) (d : ℝ)
    (hA : IsUnit (sigmaMatrix d s n))
    (hjet : ∀ k < 2*n+s+1,
      AnalyticAt ℝ (fun x => completedSigmaLogJet x k) d) :
    AnalyticAt ℝ (fun x => sigmaSchur x s n) d := by
  let A := fun x => sigmaMatrix x s n
  have hentry : ∀ i j, AnalyticAt ℝ (fun x => A x i j) d := by
    intro i j
    exact hjet (i.val+j.val+s) (by omega)
  have hdet := matrixDet_analyticAt_of_entries A d hentry
  have hdetne : (A d).det ≠ 0 := by
    exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hA)
  have hInvDet : AnalyticAt ℝ (fun x => ((A x).det)⁻¹) d := hdet.inv hdetne
  have hAdj : ∀ i j, AnalyticAt ℝ (fun x => (A x).adjugate i j) d := by
    intro i j
    have hminor : AnalyticAt ℝ
        (fun x => ((A x).updateRow j (Pi.single i (1:ℝ))).det) d := by
      apply matrixDet_analyticAt_of_entries
      intro r c
      change AnalyticAt ℝ
        (fun x => Function.update (A x) j (Pi.single i (1:ℝ)) r c) d
      simp only [Function.update_apply]
      by_cases hr : r = j
      · simp [hr]
        exact analyticAt_const
      · simp [hr]
        exact hentry r c
    have heq : (fun x : ℝ => (A x).adjugate i j) =
        (fun x => ((A x).updateRow j (Pi.single i (1:ℝ))).det) := by
      funext x
      exact Matrix.adjugate_apply (A x) i j
    exact hminor.congr (Filter.EventuallyEq.of_eq heq.symm)
  have hInvEntry : ∀ i j, AnalyticAt ℝ (fun x => (A x)⁻¹ i j) d := by
    intro i j
    have hm := hInvDet.mul (hAdj i j)
    have heq : (fun x : ℝ => (A x)⁻¹ i j) =
        (fun x => ((A x).det)⁻¹ * (A x).adjugate i j) := by
      funext x
      simp [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
    exact hm.congr (Filter.EventuallyEq.of_eq heq.symm)
  have hb : AnalyticAt ℝ
      (fun x => sourceMomentCoupling (completedSigmaLogJet x) s n) d := by
    apply AnalyticAt.pi
    intro i
    exact hjet (i.val+n+s) (by omega)
  have hc : AnalyticAt ℝ (fun x => completedSigmaLogJet x (2*n+s)) d :=
    hjet (2*n+s) (by omega)
  have hInvb : AnalyticAt ℝ
      (fun x => (A x)⁻¹ *ᵥ sourceMomentCoupling (completedSigmaLogJet x) s n) d := by
    apply AnalyticAt.pi
    intro i
    change AnalyticAt ℝ
      (fun x => ∑ j : Fin n,
        ((A x)⁻¹ i j) * (sourceMomentCoupling (completedSigmaLogJet x) s n j)) d
    have hsum : (fun x : ℝ =>
        ∑ j : Fin n, ((A x)⁻¹ i j) *
          (sourceMomentCoupling (completedSigmaLogJet x) s n j)) =
        ∑ j : Fin n, (fun x => ((A x)⁻¹ i j) *
          (sourceMomentCoupling (completedSigmaLogJet x) s n j)) := by
      funext x
      simp
    rw [hsum]
    refine Finset.analyticAt_sum (Finset.univ : Finset (Fin n)) ?_
    intro j hj
    exact (hInvEntry i j).mul (analyticAt_pi_iff.mp hb j)
  have hdot : AnalyticAt ℝ
      (fun x => sourceMomentCoupling (completedSigmaLogJet x) s n ⬝ᵥ
        ((A x)⁻¹ *ᵥ sourceMomentCoupling (completedSigmaLogJet x) s n)) d := by
    change AnalyticAt ℝ
      (fun x => ∑ i : Fin n,
        sourceMomentCoupling (completedSigmaLogJet x) s n i *
          (((A x)⁻¹ *ᵥ sourceMomentCoupling (completedSigmaLogJet x) s n) i)) d
    have hsum : (fun x : ℝ =>
        ∑ i : Fin n, sourceMomentCoupling (completedSigmaLogJet x) s n i *
          (((A x)⁻¹ *ᵥ sourceMomentCoupling (completedSigmaLogJet x) s n) i)) =
        ∑ i : Fin n, (fun x => sourceMomentCoupling (completedSigmaLogJet x) s n i *
          (((A x)⁻¹ *ᵥ sourceMomentCoupling (completedSigmaLogJet x) s n) i)) := by
      funext x
      simp
    rw [hsum]
    refine Finset.analyticAt_sum (Finset.univ : Finset (Fin n)) ?_
    intro i hi
    exact (analyticAt_pi_iff.mp hb i).mul (analyticAt_pi_iff.mp hInvb i)
  change AnalyticAt ℝ
    (fun x => completedSigmaLogJet x (2*n+s) -
      sourceMomentCoupling (completedSigmaLogJet x) s n ⬝ᵥ
        ((A x)⁻¹ *ᵥ sourceMomentCoupling (completedSigmaLogJet x) s n)) d
  exact hc.sub hdot

/-- The third transverse derivative vanishes because the original moving Schur pivot is even. -/
theorem sigmaSchur_third_deriv_center_eq_zero (s n : ℕ) :
    iteratedDeriv 3 (fun d => sigmaSchur d s n) 0 = 0 := by
  let g : ℝ → ℝ := fun d => sigmaSchur d s n
  have heven : (fun d : ℝ => g (-d)) =ᶠ[𝓝 (0:ℝ)] g := by
    have hstrip : Set.Ioo (-(1/2:ℝ)) (1/2) ∈ 𝓝 (0:ℝ) :=
      Ioo_mem_nhds (by norm_num) (by norm_num)
    filter_upwards [hstrip] with d hd
    exact sigmaSchur_even s n d hd.1 hd.2
  have hiter := heven.iteratedDeriv_eq 3
  have hzero := hiter
  rw [iteratedDeriv_comp_neg] at hzero
  norm_num [g] at hzero
  linarith

/-- A quartic local remainder for the original completed sigma Schur pivot. The constants
are existential and may depend on the sector and order; no sign of the curvature is assumed. -/
theorem exists_sigmaSchur_quartic_remainder (s n : ℕ)
    (hA0 : IsUnit (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment s n)) :
    ∃ δ B : ℝ, 0 < δ ∧ 0 ≤ B ∧ δ < 1/2 ∧
      ∀ d : ℝ, |d| ≤ δ →
        |sigmaSchur d s n - sigmaSchur 0 s n +
          sigmaSchurCurvatureAmplitude s n * d^2| ≤ B * d^4 := by
  obtain ⟨U, hUopen, hU0, hUunit, hUjet⟩ :=
    exists_sigma_prefix_neighborhood s n hA0
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hUopen 0 hU0
  let δ := min (ε/2) (1/4:ℝ)
  have hδ : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδsmall : δ < 1/2 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hsymm : Set.Icc (-δ) δ ⊆ U := by
    intro x hx
    apply hball
    have hxd : |x| ≤ δ := abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
    have hδε : δ < ε := by
      calc
        δ ≤ ε/2 := min_le_left _ _
        _ < ε := by linarith
    have hxe : |x| < ε := lt_of_le_of_lt hxd hδε
    simpa [Metric.mem_ball, Real.dist_eq] using hxe
  let g : ℝ → ℝ := fun d => sigmaSchur d s n
  have hgCont : ContDiffOn ℝ 4 g (Set.Icc (-δ) δ) := by
    intro x hx
    have hxU := hsymm hx
    have hAx : IsUnit (sigmaMatrix x s n) := hUunit x hxU
    have hjetx : ∀ k < 2*n+s+1,
        AnalyticAt ℝ (fun y => completedSigmaLogJet y k) x :=
      fun k hk => hUjet x hxU k hk
    exact (sigmaSchur_analyticAt_of_prefix s n x hAx hjetx).contDiffAt.contDiffWithinAt
  have hgContPos : ContDiffOn ℝ 4 g (Set.Icc 0 δ) := by
    intro x hx
    have hxSymm : x ∈ Set.Icc (-δ) δ :=
      ⟨(le_of_lt (neg_lt_zero.mpr hδ)).trans hx.1, hx.2⟩
    exact (hgCont x hxSymm).mono (by
      intro y hy
      exact ⟨(le_of_lt (neg_lt_zero.mpr hδ)).trans hy.1, hy.2⟩)
  obtain ⟨C, hC⟩ := exists_taylor_mean_remainder_bound
    (f := g) (a := 0) (b := δ) (n := 3) (le_of_lt hδ) hgContPos
  have hA0' : IsUnit (sigmaMatrix 0 s n) := by
    simpa [sigma_matrix_center] using hA0
  have hgAnalytic0 : AnalyticAt ℝ g 0 := by
    apply sigmaSchur_analyticAt_of_prefix s n 0 hA0'
    intro k hk
    exact sigma_log_jet_analytic_center k
  have hContAt0 : ContDiffAt ℝ 4 g 0 := hgAnalytic0.contDiffAt
  have hUnique : UniqueDiffOn ℝ (Set.Icc 0 δ) := uniqueDiffOn_Icc (by linarith)
  have hTaylor : ∀ d ∈ Set.Icc 0 δ,
      taylorWithinEval g 3 (Set.Icc 0 δ) 0 d =
        sigmaSchur 0 s n - sigmaSchurCurvatureAmplitude s n * d^2 := by
    intro d hd
    have hw1 : iteratedDerivWithin 1 g (Set.Icc 0 δ) 0 = iteratedDeriv 1 g 0 :=
      iteratedDerivWithin_eq_iteratedDeriv hUnique
        (hContAt0.of_le (by norm_num)) (by simp [hδ.le])
    have hw2 : iteratedDerivWithin 2 g (Set.Icc 0 δ) 0 = iteratedDeriv 2 g 0 :=
      iteratedDerivWithin_eq_iteratedDeriv hUnique
        (hContAt0.of_le (by norm_num)) (by simp [hδ.le])
    have hw3 : iteratedDerivWithin 3 g (Set.Icc 0 δ) 0 = iteratedDeriv 3 g 0 :=
      iteratedDerivWithin_eq_iteratedDeriv hUnique
        (hContAt0.of_le (by norm_num)) (by simp [hδ.le])
    have hderiv1 : iteratedDeriv 1 g 0 = 0 := by
      simpa [g, iteratedDeriv_one] using sigmaSchur_deriv_center s n hA0
    have hderiv2 : iteratedDeriv 2 g 0 = -2 * sigmaSchurCurvatureAmplitude s n := by
      simpa [g, sigmaSchurCurvatureAmplitude] using
        moving_schur_curvature_expanded s n hA0
    have hderiv3 : iteratedDeriv 3 g 0 = 0 :=
      sigmaSchur_third_deriv_center_eq_zero s n
    rw [taylorWithinEval_succ, taylorWithinEval_succ, taylorWithinEval_succ,
      taylor_within_zero_eval, hw1, hw2, hw3, hderiv1, hderiv2, hderiv3]
    simp only [smul_eq_mul]
    norm_num [Nat.factorial]
    ring
  let B := max C 0
  refine ⟨δ, B, hδ, le_max_right _ _, hδsmall, ?_⟩
  intro d hd
  by_cases hnonneg : 0 ≤ d
  · have hdI : d ∈ Set.Icc 0 δ := ⟨hnonneg, (le_abs_self d).trans hd⟩
    have hrem := hC d hdI
    rw [hTaylor d hdI] at hrem
    have hB : C ≤ B := le_max_left _ _
    have hpow : 0 ≤ (d - 0)^(3+1) := by positivity
    have hremB : |g d - (sigmaSchur 0 s n -
        sigmaSchurCurvatureAmplitude s n * d^2)| ≤ B * d^4 := by
      simpa [Real.norm_eq_abs, sub_zero] using hrem.trans (mul_le_mul_of_nonneg_right hB hpow)
    have hform : g d - (sigmaSchur 0 s n -
        sigmaSchurCurvatureAmplitude s n * d^2) =
        sigmaSchur d s n - sigmaSchur 0 s n +
          sigmaSchurCurvatureAmplitude s n * d^2 := by
      dsimp [g]
      ring
    rw [hform] at hremB
    exact hremB
  · have hneg : d < 0 := lt_of_not_ge hnonneg
    have hdabs := abs_le.mp hd
    have hdneg : -d ∈ Set.Icc 0 δ := by
      constructor
      · linarith
      · simpa [abs_of_neg hneg] using hd
    have hparity := sigmaSchur_even s n d
      (by linarith [hdabs.1, hδsmall]) (by linarith [hdabs.2, hδsmall])
    have hpos := hC (-d) hdneg
    rw [hTaylor (-d) hdneg] at hpos
    have hB : C ≤ B := le_max_left _ _
    have hbase : 0 ≤ -d - 0 := by linarith
    have hpow : 0 ≤ (-d - 0)^(3+1) := pow_nonneg hbase _
    have hposB : |g (-d) - (sigmaSchur 0 s n -
        sigmaSchurCurvatureAmplitude s n * (-d)^2)| ≤ B * (-d)^4 := by
      simpa [Real.norm_eq_abs, sub_zero] using hpos.trans (mul_le_mul_of_nonneg_right hB hpow)
    have heq : g (-d) - (sigmaSchur 0 s n -
        sigmaSchurCurvatureAmplitude s n * (-d)^2) =
        sigmaSchur d s n - sigmaSchur 0 s n +
          sigmaSchurCurvatureAmplitude s n * d^2 := by
      dsimp [g]
      rw [hparity]
      ring
    calc
      |sigmaSchur d s n - sigmaSchur 0 s n +
          sigmaSchurCurvatureAmplitude s n * d^2| =
        |g (-d) - (sigmaSchur 0 s n -
          sigmaSchurCurvatureAmplitude s n * (-d)^2)| := by rw [← heq]
      _ ≤ B * (-d)^4 := hposB
      _ = B * d^4 := by ring

/-- Quantitative endpoint gate supplied by the quartic theorem. Once source interval bounds
discharge either displayed margin, the corresponding pivot sign follows without a Hankel-sign
assumption. -/
theorem exists_sigmaSchur_quartic_sign_gate (s n : ℕ)
    (hA0 : IsUnit (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment s n)) :
    ∃ δ B : ℝ, 0 < δ ∧ 0 ≤ B ∧ δ < 1/2 ∧
      (∀ d : ℝ, |d| ≤ δ →
        0 < sigmaSchur 0 s n - sigmaSchurCurvatureAmplitude s n*d^2 - B*d^4 →
          0 < sigmaSchur d s n) ∧
      (∀ d : ℝ, |d| ≤ δ →
        sigmaSchur 0 s n - sigmaSchurCurvatureAmplitude s n*d^2 + B*d^4 < 0 →
          sigmaSchur d s n < 0) := by
  obtain ⟨δ, B, hδ, hB, hδsmall, hrem⟩ := exists_sigmaSchur_quartic_remainder s n hA0
  refine ⟨δ, B, hδ, hB, hδsmall, ?_, ?_⟩
  · intro d hd hmargin
    have herror := hrem d hd
    have hlo := (abs_le.mp herror).1
    have hrepr : sigmaSchur d s n =
        sigmaSchur 0 s n - sigmaSchurCurvatureAmplitude s n*d^2 +
          (sigmaSchur d s n - sigmaSchur 0 s n +
            sigmaSchurCurvatureAmplitude s n*d^2) := by ring
    rw [hrepr]
    linarith
  · intro d hd hmargin
    have herror := hrem d hd
    have hhi := (abs_le.mp herror).2
    have hrepr : sigmaSchur d s n =
        sigmaSchur 0 s n - sigmaSchurCurvatureAmplitude s n*d^2 +
          (sigmaSchur d s n - sigmaSchur 0 s n +
            sigmaSchurCurvatureAmplitude s n*d^2) := by ring
    rw [hrepr]
    linarith

end
end CarryMovingSigma

#print axioms CarryMovingSigma.sigmaSchur_fixed_direction_exact
#print axioms CarryMovingSigma.sigmaSchur_fixed_direction_residual_form
#print axioms CarryMovingSigma.sigmaSchur_le_fixed_direction_of_posDef
#print axioms CarryMovingSigma.exists_sigmaSchur_quartic_remainder
#print axioms CarryMovingSigma.exists_sigmaSchur_quartic_sign_gate
