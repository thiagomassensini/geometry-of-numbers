import PrimeClockBridge

/-! A source-derived overlap on the material edge 2 → 3. This tests the
actual prime channels, not arbitrary fields or an anticipated Hankel matrix.
The result concerns the stated finite prefix; tails remain in PrimeClockBridge. -/
namespace CarryPrimeClock
open CarrySelfAdjointOperator GeometryOfNumbers.Analysis NativeCarryC3Crosswalk
open GeometryOfNumbers.Analysis.BaseTwoCompletion
open NativeCarrySpectralWeyl.Camera CPFormal.Analytic.Cp CPFormal.Carry.Cp
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

def logTwo (t : ℝ) : ℂ := positiveLogDirichletValue (nativeLine t) 1
def logThree (t : ℝ) : ℂ := positiveLogDirichletValue (nativeLine t) 2

theorem prime_two_channel (t : ℝ) :
    cameraResolvedLogSlopeChannel 2 t 2 =
      lp.single 2 0 (logTwo t) - lp.single 2 1 (logTwo t) := by
  apply lp.ext
  funext n
  by_cases h0 : n = 0
  · subst n
    norm_num [cameraResolvedLogSlopeChannel_apply, cameraResolvedLogDirichletGradient_apply, cameraResolvedLogDirichletValue_apply, cameraLogContributionVectorComplex_apply, Nat.prime_two.factorization, Nat.prime_three.factorization, positiveLogDirichletValue, lp.coeFn_single, Pi.single_apply, eq_comm, logTwo]
    ring
  by_cases h1 : n = 1
  · subst n
    norm_num [cameraResolvedLogSlopeChannel_apply, cameraResolvedLogDirichletGradient_apply, cameraResolvedLogDirichletValue_apply, cameraLogContributionVectorComplex_apply, Nat.prime_two.factorization, Nat.prime_three.factorization, positiveLogDirichletValue, lp.coeFn_single, Pi.single_apply, eq_comm, logTwo]
    ring
  · have hn : ¬ n < 2 := by omega
    simp [cameraResolvedLogSlopeChannel_apply, hn, h0, h1, eq_comm]

theorem prime_three_channel (t : ℝ) :
    cameraResolvedLogSlopeChannel 2 t 3 = lp.single 2 1 (logThree t) := by
  apply lp.ext
  funext n
  by_cases h0 : n = 0
  · subst n
    norm_num [cameraResolvedLogSlopeChannel_apply, cameraResolvedLogDirichletGradient_apply, cameraResolvedLogDirichletValue_apply, cameraLogContributionVectorComplex_apply, Nat.prime_two.factorization, Nat.prime_three.factorization, positiveLogDirichletValue, lp.coeFn_single, Pi.single_apply, eq_comm, logThree]
  by_cases h1 : n = 1
  · subst n
    norm_num [cameraResolvedLogSlopeChannel_apply, cameraResolvedLogDirichletGradient_apply, cameraResolvedLogDirichletValue_apply, cameraLogContributionVectorComplex_apply, Nat.prime_two.factorization, Nat.prime_three.factorization, positiveLogDirichletValue, lp.coeFn_single, Pi.single_apply, eq_comm, logThree]
    ring
  · have hn : ¬ n < 2 := by omega
    simp [cameraResolvedLogSlopeChannel_apply, hn, h1, eq_comm]

/-- Ordered, two-time crossing from the shared physical edge. -/
theorem prime_two_three_crossing (t u : ℝ) :
    inner ℂ (cameraResolvedLogSlopeChannel 2 t 2)
      (cameraResolvedLogSlopeChannel 2 u 3) = -conj (logTwo t)*logThree u := by
  rw [prime_two_channel, prime_three_channel, inner_sub_left]
  simp [lp.inner_single_left, RCLike.inner_apply]
  ring

theorem coherentPrefix_two (t : ℝ) :
    coherentPrefix 2 t = cameraResolvedLogSlopeChannel 2 t 2 +
      cameraResolvedLogSlopeChannel 2 t 3 := by
  rw [coherentPrefix_eq_tfvd, prime_two_channel, prime_three_channel]
  apply lp.ext
  funext n
  rw [canonicalCompletedC3LogJetPrefixState_apply]
  by_cases h0 : n = 0
  · subst n
    simp [positiveLogDirichletGradient, logTwo, logThree, lp.coeFn_single]
  by_cases h1 : n = 1
  · subst n
    simp [positiveLogDirichletGradient, logTwo, logThree, lp.coeFn_single]
    ring
  · have hn : ¬ n < 2 := by omega
    simp [hn, h0, h1, lp.coeFn_single]

/-- The family has the inherited DIRECT-SUM metric. Its coherent synthesis
has a different pairing because its prime channels overlap. -/
def twoPrimeFamily (t : ℝ) : FiniteHilbertFamily (Fin 2) MaterialEdgeL2 :=
  WithLp.toLp 2 (fun i => if i = 0 then cameraResolvedLogSlopeChannel 2 t 2
    else cameraResolvedLogSlopeChannel 2 t 3)

theorem twoPrimeFamily_pairing (t u : ℝ) :
    inner ℂ (twoPrimeFamily t) (twoPrimeFamily u) =
      inner ℂ (cameraResolvedLogSlopeChannel 2 t 2) (cameraResolvedLogSlopeChannel 2 u 2) +
      inner ℂ (cameraResolvedLogSlopeChannel 2 t 3) (cameraResolvedLogSlopeChannel 2 u 3) := by
  simp [twoPrimeFamily, PiLp.inner_apply, Fin.sum_univ_two]

/-- Exact defect: whitening the outer ledger preserves its direct-sum Gram;
it does not automatically produce the coherent physical synthesis Gram. -/
theorem whitened_coherent_pairing_defect
    {state : Type*} [Fintype state] (C : Matrix (Fin 2) state ℝ)
    (hG : (finiteCameraRowGram C).PosDef) (t u : ℝ) :
    inner ℂ (finiteCanonicalCameraHilbertSynthesis C (twoPrimeFamily t))
      (finiteCanonicalCameraHilbertSynthesis C (twoPrimeFamily u)) -
        inner ℂ (coherentPrefix 2 t) (coherentPrefix 2 u) =
      conj (logTwo t)*logThree u + conj (logThree t)*logTwo u := by
  rw [finiteCanonicalCameraHilbertSynthesis_isometry C hG,
    twoPrimeFamily_pairing, coherentPrefix_two t, coherentPrefix_two u]
  simp only [inner_add_left, inner_add_right]
  rw [prime_two_three_crossing]
  have h := inner_conj_symm (𝕜 := ℂ) (cameraResolvedLogSlopeChannel 2 t 3)
    (cameraResolvedLogSlopeChannel 2 u 2)
  rw [prime_two_three_crossing] at h
  rw [← h]
  simp only [map_neg, map_mul, Complex.conj_conj]
  ring

theorem positiveDirichlet_eq_material_sample (t : ℝ) (n : ℕ) :
    positiveDirichletValue (nativeLine t) n = criticalMaterialSample t (n+1) := by
  rw [criticalMaterialSample_eq_cpow t (by omega)]
  unfold positiveDirichletValue
  congr 1
  simp only [criticalMaterialExponent, nativeLine]
  ring

theorem logTwo_zero : logTwo 0 = ((Real.log 2/Real.sqrt 2 : ℝ) : ℂ) := by
  rw [logTwo, positiveLogDirichletValue, positiveDirichlet_eq_material_sample]
  simp [criticalMaterialSample, div_eq_mul_inv]

theorem logThree_zero : logThree 0 = ((Real.log 3/Real.sqrt 3 : ℝ) : ℂ) := by
  rw [logThree, positiveLogDirichletValue, positiveDirichlet_eq_material_sample]
  simp [criticalMaterialSample, div_eq_mul_inv]

theorem prime_two_three_crossing_zero_negative :
    (inner ℂ (cameraResolvedLogSlopeChannel 2 0 2)
      (cameraResolvedLogSlopeChannel 2 0 3)).re < 0 := by
  rw [prime_two_three_crossing, logTwo_zero, logThree_zero]
  simp only [Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_neg, Complex.ofReal_re]
  have h2 : 0 < Real.log 2/Real.sqrt 2 := div_pos (Real.log_pos (by norm_num))
    (Real.sqrt_pos.mpr (by norm_num))
  have h3 : 0 < Real.log 3/Real.sqrt 3 := div_pos (Real.log_pos (by norm_num))
    (Real.sqrt_pos.mpr (by norm_num))
  nlinarith

theorem whitened_coherent_origin_gap
    {state : Type*} [Fintype state] (C : Matrix (Fin 2) state ℝ)
    (hG : (finiteCameraRowGram C).PosDef) :
    ‖finiteCanonicalCameraHilbertSynthesis C (twoPrimeFamily 0)‖^2 -
      ‖coherentPrefix 2 0‖^2 =
        2*(Real.log 2/Real.sqrt 2)*(Real.log 3/Real.sqrt 3) := by
  have h := congrArg Complex.re (whitened_coherent_pairing_defect C hG 0 0)
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K,
    logTwo_zero, logThree_zero] at h
  simp only [Complex.sub_re, Complex.conj_ofReal, ← Complex.ofReal_mul,
    ← Complex.ofReal_add, Complex.ofReal_re] at h
  simp only [← RCLike.ofReal_pow] at h
  change ‖finiteCanonicalCameraHilbertSynthesis C (twoPrimeFamily 0)‖^2 -
      ‖coherentPrefix 2 0‖^2 =
      (Real.log 2/Real.sqrt 2)*(Real.log 3/Real.sqrt 3) +
      (Real.log 3/Real.sqrt 3)*(Real.log 2/Real.sqrt 2) at h
  nlinarith only [h]

theorem whitened_coherent_origin_ne
    {state : Type*} [Fintype state] (C : Matrix (Fin 2) state ℝ)
    (hG : (finiteCameraRowGram C).PosDef) :
    ‖finiteCanonicalCameraHilbertSynthesis C (twoPrimeFamily 0)‖^2 ≠
      ‖coherentPrefix 2 0‖^2 := by
  have h := whitened_coherent_origin_gap C hG
  have h2 : 0 < Real.log 2/Real.sqrt 2 := div_pos (Real.log_pos (by norm_num))
    (Real.sqrt_pos.mpr (by norm_num))
  have h3 : 0 < Real.log 3/Real.sqrt 3 := div_pos (Real.log_pos (by norm_num))
    (Real.sqrt_pos.mpr (by norm_num))
  intro he
  rw [he, sub_self] at h
  nlinarith

end
end CarryPrimeClock
