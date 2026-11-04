import RawRankOne
import CarrySelfAdjointOperator.CompletedNativeChiralReturnMixedSourceJets
import CarrySelfAdjointOperator.CompletedNativeHerglotzFourthOrderGate

namespace CarryCauchyResidual
open CarrySelfAdjointOperator ChiralReturn CarryReturnDeflation CarryPositiveSquare
open Filter Topology
open scoped InnerProductSpace ComplexConjugate BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000

theorem nativeSourceOddBoundaryCoefficient_zero_eq_two_moment :
    (nativeSourceOddBoundaryCoefficient 0 : ℝ) =
      2 * canonicalCompletedNativeLogDerivativeMoment 0 := by
  obtain ⟨h0, _, _, _⟩ := nativeSourceOddBoundaryCoefficient_integral_formulas
  have ha : 0 < completedNativeXiCosineMoment 0 := completedNativeXiCosineMoment_pos 0
  have hc0 : completedNativeRealEvenCharacteristicCoefficient 0 =
      completedNativeXiCosineMoment 0 :=
    completedNativeRealEvenCharacteristicCoefficient_zero_eq_xiCosineMoment
  have hc1 : completedNativeRealEvenCharacteristicCoefficient 1 =
      -completedNativeXiCosineMoment 1 / 2 := by
    norm_num [completedNativeRealEvenCharacteristicCoefficient,
      completedNativeEvenCharacteristicCoefficient, completedGreenTaylorJet,
      iteratedDeriv_two_completedNativeOperatorCharacteristic_zero] ; ring
  rw [h0, canonicalCompletedNativeLogDerivativeMoment_zero_eq_secondOrderRatio,
    hc0, hc1]
  have ha' : (completedNativeXiCosineMoment 0 : ℝ) ≠ 0 := ha.ne'
  field_simp [ha']

theorem nativeSourceOddBoundaryCoefficient_one_eq_two_moment :
    (nativeSourceOddBoundaryCoefficient 1 : ℝ) =
      2 * canonicalCompletedNativeLogDerivativeMoment 1 := by
  obtain ⟨_, h1, _, _⟩ := nativeSourceOddBoundaryCoefficient_integral_formulas
  have ha : 0 < completedNativeXiCosineMoment 0 := completedNativeXiCosineMoment_pos 0
  have hc0 : completedNativeRealEvenCharacteristicCoefficient 0 =
      completedNativeXiCosineMoment 0 :=
    completedNativeRealEvenCharacteristicCoefficient_zero_eq_xiCosineMoment
  have hc1 : completedNativeRealEvenCharacteristicCoefficient 1 =
      -completedNativeXiCosineMoment 1 / 2 := by
    norm_num [completedNativeRealEvenCharacteristicCoefficient,
      completedNativeEvenCharacteristicCoefficient, completedGreenTaylorJet,
      iteratedDeriv_two_completedNativeOperatorCharacteristic_zero] ; ring
  have hc2 : completedNativeRealEvenCharacteristicCoefficient 2 =
      completedNativeXiCosineMoment 2 / 24 := by
    norm_num [completedNativeRealEvenCharacteristicCoefficient,
      completedNativeEvenCharacteristicCoefficient, completedGreenTaylorJet,
      iteratedDeriv_four_completedNativeOperatorCharacteristic_zero] ; ring
  rw [h1, canonicalCompletedNativeLogDerivativeMoment_one_eq_fourthOrderDiscriminant,
    hc0, hc1, hc2]
  have ha' : (completedNativeXiCosineMoment 0 : ℝ) ≠ 0 := ha.ne'
  field_simp [ha']
  ring_nf

def nativeTransverseLogSlope (h : ℂ) : ℂ :=
  -Complex.I * completedNativeOperatorLogDerivative (Complex.I*h)

theorem nativeTransverseLogSlope_first_two_remainder :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧ ∀ᶠ h : ℂ in nhds 0,
      nativeTransverseLogSlope h =
        (2*(canonicalCompletedNativeLogDerivativeMoment 0:ℂ))*h -
          (2*(canonicalCompletedNativeLogDerivativeMoment 1:ℂ))*h^3 + h^5*R h := by
  obtain ⟨R₀, hR₀, hR₀eq⟩ := nativeSourceTransverseSlope_exact_remainder
  let R : ℂ → ℂ := fun h =>
    (nativeSourceOddBoundaryCoefficient 2:ℂ) -
      (nativeSourceOddBoundaryCoefficient 3:ℂ)*h^2 + h^3*R₀ h
  have hR : AnalyticAt ℂ R 0 := by
    dsimp [R]
    fun_prop
  refine ⟨R, hR, ?_⟩
  filter_upwards [hR₀eq] with h hh
  change -Complex.I * completedNativeOperatorLogDerivative (Complex.I*h) = _
  rw [hh]
  dsimp [R]
  norm_num [Finset.sum_range_succ, Nat.reduceMul, Nat.reduceAdd,
    smul_eq_mul]
  rw [nativeSourceOddBoundaryCoefficient_zero_eq_two_moment,
    nativeSourceOddBoundaryCoefficient_one_eq_two_moment]
  norm_cast
  ring

def nativeTransverseChiralQuotient (h : ℂ) : ℂ :=
  completedNativeHermiteBiehlerChiralQuotient (Complex.I*h)

theorem nativeTransverseChiralQuotient_eq_cayley_eventually :
    ∀ᶠ h : ℂ in nhds 0,
      nativeTransverseChiralQuotient h =
        (nativeTransverseLogSlope h - 1) /
          (nativeTransverseLogSlope h + 1) ∧
      nativeTransverseLogSlope h + 1 ≠ 0 := by
  have hline : Tendsto (fun h : ℂ => Complex.I*h) (nhds 0) (nhds 0) := by
    simpa only [id_eq, mul_zero] using
      (Filter.tendsto_id : Tendsto (fun h : ℂ => h) (nhds 0) (nhds 0)).const_mul Complex.I
  filter_upwards [hline.eventually completedNativeChiralPickFactorization_eventually_regular]
      with h hreg
  rcases hreg with ⟨_, hF, hpositive⟩
  have hcoord := completedNativePositiveHermiteBiehlerCoordinate_eq_characteristic_mul_herglotz_add_I hF
  have hLA : completedNativeOperatorLogDerivative (Complex.I*h) + Complex.I ≠ 0 := by
    rw [hcoord] at hpositive
    exact (mul_ne_zero_iff.mp hpositive).2
  have hsden : nativeTransverseLogSlope h + 1 ≠ 0 := by
    have hmul := mul_ne_zero (show (-Complex.I : ℂ) ≠ 0 by simp) hLA
    have hI : Complex.I * Complex.I = -1 := by
      norm_num
    have heq : -Complex.I *
        (completedNativeOperatorLogDerivative (Complex.I*h) + Complex.I) =
        nativeTransverseLogSlope h + 1 := by
      dsimp [nativeTransverseLogSlope]
      simp [mul_add, neg_mul, hI]
    rw [← heq]
    exact hmul
  refine ⟨?_, hsden⟩
  change completedNativeHermiteBiehlerChiralQuotient (Complex.I*h) = _
  rw [completedNativeHermiteBiehlerChiralQuotient_eq_cayley hF]
  simp only [completedNativeLogDerivativeHerglotzCoordinate_eq_operatorLogDerivative]
  change (completedNativeOperatorLogDerivative (Complex.I*h) - Complex.I) /
      (completedNativeOperatorLogDerivative (Complex.I*h) + Complex.I) =
    ((-Complex.I)*completedNativeOperatorLogDerivative (Complex.I*h) - 1) /
      ((-Complex.I)*completedNativeOperatorLogDerivative (Complex.I*h) + 1)
  calc
    _ = ((-Complex.I)*(completedNativeOperatorLogDerivative (Complex.I*h)-Complex.I)) /
        ((-Complex.I)*(completedNativeOperatorLogDerivative (Complex.I*h)+Complex.I)) := by
      field_simp [hLA]
    _ = _ := by
      have hI : Complex.I * Complex.I = -1 := by
        norm_num
      congr 1 <;> simp [mul_sub, mul_add, neg_mul, hI]

def nativeSourceRemainderP (R : ℂ → ℂ) (a b h : ℂ) : ℂ :=
  a - b*h^2 + h^4*R h

def nativeSourceRemainderD (R : ℂ → ℂ) (b h : ℂ) : ℂ :=
  -b + h^2*R h

def nativeCayleyCubicRemainder (R : ℂ → ℂ) (a b h : ℂ) : ℂ :=
  2*h*R h - 4*a*nativeSourceRemainderD R b h -
    2*h^2*(nativeSourceRemainderD R b h)^2 +
    2*h*nativeSourceRemainderD R b h *
      ((nativeSourceRemainderP R a b h)^2 +
        a*nativeSourceRemainderP R a b h + a^2) -
    2*(nativeSourceRemainderP R a b h)^4 /
      (1 + h*nativeSourceRemainderP R a b h)

theorem nativeCayleyCubicRemainder_analytic {R : ℂ → ℂ} {a b : ℂ}
    (hR : AnalyticAt ℂ R 0) :
    AnalyticAt ℂ (nativeCayleyCubicRemainder R a b) 0 := by
  have hp : AnalyticAt ℂ (fun h => nativeSourceRemainderP R a b h) 0 := by
    dsimp [nativeSourceRemainderP]
    fun_prop
  have hd : AnalyticAt ℂ (fun h => nativeSourceRemainderD R b h) 0 := by
    dsimp [nativeSourceRemainderD]
    fun_prop
  have hden : AnalyticAt ℂ
      (fun h => 1 + h*nativeSourceRemainderP R a b h) 0 := by
    fun_prop
  have hden0 : (1 + (0:ℂ)*nativeSourceRemainderP R a b 0) ≠ 0 := by
    norm_num
  have hquot : AnalyticAt ℂ
      (fun h => 2*(nativeSourceRemainderP R a b h)^4 /
        (1 + h*nativeSourceRemainderP R a b h)) 0 := by
    have hn : AnalyticAt ℂ
        (fun h => 2*(nativeSourceRemainderP R a b h)^4) 0 := by fun_prop
    exact hn.div hden hden0
  have hpartial : AnalyticAt ℂ (fun h =>
      2*h*R h - 4*a*nativeSourceRemainderD R b h -
        2*h^2*(nativeSourceRemainderD R b h)^2 +
        2*h*nativeSourceRemainderD R b h *
          ((nativeSourceRemainderP R a b h)^2 +
            a*nativeSourceRemainderP R a b h + a^2)) 0 := by
    fun_prop
  change AnalyticAt ℂ (fun h =>
      2*h*R h - 4*a*nativeSourceRemainderD R b h -
        2*h^2*(nativeSourceRemainderD R b h)^2 +
        2*h*nativeSourceRemainderD R b h *
          ((nativeSourceRemainderP R a b h)^2 +
            a*nativeSourceRemainderP R a b h + a^2) -
        2*(nativeSourceRemainderP R a b h)^4 /
          (1+h*nativeSourceRemainderP R a b h)) 0
  exact hpartial.sub hquot

theorem nativeTransverseChiralQuotient_cubic_remainder :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧ ∀ᶠ h : ℂ in nhds 0,
      nativeTransverseChiralQuotient h =
        -1 + (4*(canonicalCompletedNativeLogDerivativeMoment 0:ℂ))*h -
          (8*(canonicalCompletedNativeLogDerivativeMoment 0:ℂ)^2)*h^2 +
          (16*(canonicalCompletedNativeLogDerivativeMoment 0:ℂ)^3 -
            4*(canonicalCompletedNativeLogDerivativeMoment 1:ℂ))*h^3 + h^4*R h := by
  obtain ⟨R₀, hR₀, hs⟩ := nativeTransverseLogSlope_first_two_remainder
  let a : ℂ := 2*(canonicalCompletedNativeLogDerivativeMoment 0:ℂ)
  let b : ℂ := 2*(canonicalCompletedNativeLogDerivativeMoment 1:ℂ)
  let R : ℂ → ℂ := nativeCayleyCubicRemainder R₀ a b
  have hR : AnalyticAt ℂ R 0 := by
    dsimp [R]
    exact nativeCayleyCubicRemainder_analytic hR₀
  refine ⟨R, hR, ?_⟩
  filter_upwards [hs, nativeTransverseChiralQuotient_eq_cayley_eventually]
      with h hs hc
  rcases hc with ⟨hc, hden⟩
  have hsource : nativeTransverseLogSlope h =
      h*nativeSourceRemainderP R₀ a b h := by
    rw [hs]
    dsimp [nativeSourceRemainderP, a, b]
    ring
  have hden' : h*nativeSourceRemainderP R₀ a b h + 1 ≠ 0 := by
    have htemp := hden
    rw [hsource] at htemp
    simpa [add_comm] using htemp
  have hden'' : 1 + h*(a-b*h^2+h^4*R₀ h) ≠ 0 := by
    simpa [nativeSourceRemainderP, add_comm] using hden'
  have hdenInv : 1 + h*nativeSourceRemainderP R₀ a b h ≠ 0 := by
    simpa [add_comm] using hden'
  have halg :
      (h*nativeSourceRemainderP R₀ a b h - 1) /
          (h*nativeSourceRemainderP R₀ a b h + 1) =
        -1 + 2*a*h - 2*a^2*h^2 + 2*(a^3-b)*h^3 +
          h^4*nativeCayleyCubicRemainder R₀ a b h := by
    dsimp only [nativeCayleyCubicRemainder]
    field_simp [hden', hdenInv]
    dsimp [nativeSourceRemainderP, nativeSourceRemainderD]
    ring
  calc
    nativeTransverseChiralQuotient h =
        (nativeTransverseLogSlope h - 1) /
          (nativeTransverseLogSlope h + 1) := hc
    _ = (h*nativeSourceRemainderP R₀ a b h - 1) /
          (h*nativeSourceRemainderP R₀ a b h + 1) := by rw [hsource]
    _ = -1 + 2*a*h - 2*a^2*h^2 + 2*(a^3-b)*h^3 +
          h^4*nativeCayleyCubicRemainder R₀ a b h := halg
    _ = -1 + (4*(canonicalCompletedNativeLogDerivativeMoment 0:ℂ))*h -
          (8*(canonicalCompletedNativeLogDerivativeMoment 0:ℂ)^2)*h^2 +
          (16*(canonicalCompletedNativeLogDerivativeMoment 0:ℂ)^3 -
            4*(canonicalCompletedNativeLogDerivativeMoment 1:ℂ))*h^3 + h^4*R h := by
      dsimp [R, a, b]
      ring

def nativeFirstOddJetDirection : Fin 2 → ℂ := Pi.single 1 1

theorem canonicalBoundaryPair_firstOddJet_self :
    canonicalBoundaryPair 1 nativeFirstOddJetDirection nativeFirstOddJetDirection =
      (canonicalCompletedNativeLogDerivativeMoment 1:ℂ) := by
  simp [canonicalBoundaryPair, nativeFirstOddJetDirection,
    nativeSourceEvenBoundaryPhase, nativeSourceOddBoundaryPhase,
    nativeSourceEvenBoundaryIndex, nativeSourceOddBoundaryIndex]

theorem canonicalBoundaryPair_head_firstOddJet :
    canonicalBoundaryPair 1 (headBoundary 0) nativeFirstOddJetDirection = 0 := by
  rw [headBoundary_eq_single]
  simp [canonicalBoundaryPair, nativeFirstOddJetDirection,
    nativeSourceEvenBoundaryPhase, nativeSourceOddBoundaryPhase,
    nativeSourceEvenBoundaryIndex, nativeSourceOddBoundaryIndex]

theorem nativeRawJetSchur_firstOdd_tendsto :
    Tendsto (fun k => nativeRawSchurForm k 1
      (nativeSourceChiralJetInput 1 k nativeFirstOddJetDirection)
      (nativeSourceChiralJetInput 1 k nativeFirstOddJetDirection)) atTop
      (nhds (2*(canonicalCompletedNativeLogDerivativeMoment 1:ℂ))) := by
  have h := nativeRawJetSchur_tendsto_canonical 0
    nativeFirstOddJetDirection nativeFirstOddJetDirection
  rw [canonicalBoundaryPair_firstOddJet_self,
    canonicalBoundaryPair_head_firstOddJet] at h
  simpa using h

theorem remainingPair_smul_smul (k N : ℕ) (a b : ℂ)
    (c d : Fin N → ℂ) :
    remainingPair k N (a • c) (b • d) =
      star a*b*remainingPair k N c d := by
  simp [remainingPair, inner_smul_left, inner_smul_right]
  ring

theorem remainingPair_two_source_tail_scale (k : ℕ)
    (c : Fin 2 → ℂ) :
    remainingPair k 2 c c =
      star (c 1)*c 1*
        remainingPair k 2 (Pi.single 1 (1:ℂ)) (Pi.single 1 (1:ℂ)) := by
  rw [remainingPair_eraseHead k 1 c c]
  have htail : eraseHead c = tailInput (c 1 • (Pi.single 0 (1:ℂ) : Fin 1 → ℂ)) := by
    rw [eraseHead_eq_tail]
    congr 1
    funext i
    fin_cases i
    simp [tailCoefficients]
  have htail' : tailInput (c 1 • (Pi.single 0 (1:ℂ) : Fin 1 → ℂ)) =
      c 1 • (Pi.single 1 (1:ℂ) : Fin 2 → ℂ) := by
    funext i
    fin_cases i <;> simp [tailInput]
  rw [htail, htail', remainingPair_smul_smul]

/-- In the two-source physical Schur complement, the head coefficient is
discarded by the exact physical deflation.  The surviving raw Schur form is
homogeneous in the tail coefficient. -/
theorem nativeRawSchurForm_two_source_tail_scale (k : ℕ)
    (hd : oneDeficit k ≠ 0) (c : Fin 2 → ℂ) :
    nativeRawSchurForm k 1 c c =
      star (c 1)*c 1 *
        nativeRawSchurForm k 1 (Pi.single 1 (1:ℂ)) (Pi.single 1 (1:ℂ)) := by
  rw [nativeRawSchurForm_eq_remainingPair k 1 c c hd,
    nativeRawSchurForm_eq_remainingPair k 1
      (Pi.single 1 (1:ℂ)) (Pi.single 1 (1:ℂ)) hd]
  rw [remainingPair_two_source_tail_scale]
  ring

theorem nativeRawSchurForm_two_source_tail_scale_eventually
    (c : Fin 2 → ℂ) :
    ∀ᶠ k : ℕ in atTop,
      nativeRawSchurForm k 1 c c =
        star (c 1)*c 1 *
          nativeRawSchurForm k 1 (Pi.single 1 (1:ℂ)) (Pi.single 1 (1:ℂ)) := by
  filter_upwards [oneDeficit_eventually_pos] with k hk
  exact nativeRawSchurForm_two_source_tail_scale k (ne_of_gt hk) c

/-- The existing first odd jet direction has one physical tail coordinate.
This names that coefficient without replacing the original jet map. -/
def nativeFirstOddJetTailScale (k : ℕ) : ℂ :=
  nativeSourceChiralJetInput 1 k nativeFirstOddJetDirection 1

theorem nativeFirstOddJetTailScale_eq_original_factor (k : ℕ) :
    nativeFirstOddJetTailScale k =
      completedNativeNormalizedPositiveChiralAmplitude
        (canonicalCompletedC3RadialTiltPoint k 1) *
        (canonicalCompletedC3RadialSecondStep k)⁻¹ := by
  simp [nativeFirstOddJetTailScale, nativeFirstOddJetDirection,
    nativeSourceChiralJetInput, nativeSourceChiralJetInputMatrix,
    nativeSourceJetOrderPhase, completedGreenForwardWeight]

/-- With the original radial step, the first odd jet coefficient has the
normalization `K / sqrt 2` asymptotically.  This is read from the completed
amplitude at the center; no power of `K` is fitted to the Schur limit. -/
theorem nativeFirstOddJetTailScale_mul_greenStep_tendsto :
    Tendsto (fun k => nativeFirstOddJetTailScale k * canonicalGreenJetStep k)
      atTop (nhds (((Real.sqrt 2 : ℝ)⁻¹ : ℂ))) := by
  have hF := completedNativeOperatorCharacteristic_analyticAt
    zero_mem_completedNativeHeightDomain
  have hF0 : completedNativeOperatorCharacteristic 0 ≠ 0 :=
    completedNativeOperatorCharacteristic_zero_ne_zero
  have hFderiv0 : deriv completedNativeOperatorCharacteristic 0 = 0 :=
    deriv_zero_of_eventually_even completedNativeOperatorCharacteristic
      completedNativeOperatorCharacteristic_eventually_even
  have hAmplitude : ContinuousAt completedNativeNormalizedPositiveChiralAmplitude 0 := by
    unfold completedNativeNormalizedPositiveChiralAmplitude
    have hnormalizer : AnalyticAt ℂ
        canonicalCompletedC3FullWronskianChiralNormalization 0 := by
      unfold canonicalCompletedC3FullWronskianChiralNormalization
      have hsqrt : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0:ℝ)<2)).ne'
      exact (analyticAt_const.mul hF).inv
        (mul_ne_zero hsqrt hF0)
    have hpositive : AnalyticAt ℂ
        completedNativePositiveHermiteBiehlerCoordinate 0 := by
      unfold completedNativePositiveHermiteBiehlerCoordinate
      exact hF.deriv.neg.add (analyticAt_const.mul hF)
    exact hnormalizer.mul hpositive |>.continuousAt
  have hpoint := canonicalCompletedC3RadialTiltPoint_tendsto_zero 1
  have hAmplitudeLimit := hAmplitude.tendsto.comp hpoint
  have hAmplitudeZero : completedNativeNormalizedPositiveChiralAmplitude 0 =
      Complex.I * (((Real.sqrt 2 : ℝ)⁻¹ : ℂ)) := by
    unfold completedNativeNormalizedPositiveChiralAmplitude
      canonicalCompletedC3FullWronskianChiralNormalization
      completedNativePositiveHermiteBiehlerCoordinate
    simp [hFderiv0]
    field_simp [hF0]
  have hA : Tendsto
      (fun k => completedNativeNormalizedPositiveChiralAmplitude
        (canonicalCompletedC3RadialTiltPoint k 1) / Complex.I)
      atTop (nhds (((Real.sqrt 2 : ℝ)⁻¹ : ℂ))) := by
    have h := hAmplitudeLimit.div_const Complex.I
    simpa [hAmplitudeZero] using h
  have hscale : ∀ k,
      nativeFirstOddJetTailScale k * canonicalGreenJetStep k =
        completedNativeNormalizedPositiveChiralAmplitude
          (canonicalCompletedC3RadialTiltPoint k 1) / Complex.I := by
    intro k
    rw [nativeFirstOddJetTailScale_eq_original_factor,
      canonicalCompletedC3RadialSecondStep]
    unfold canonicalGreenJetStep
    field_simp [Complex.I_ne_zero,
      (show ((k:ℂ)+1) ≠ 0 by exact_mod_cast Nat.succ_ne_zero k)]
  simpa only [hscale] using hA

theorem nativeFirstOddJetTailScale_absSq_mul_greenStep_sq_tendsto :
    Tendsto (fun k => star (nativeFirstOddJetTailScale k * canonicalGreenJetStep k) *
        (nativeFirstOddJetTailScale k * canonicalGreenJetStep k))
      atTop (nhds ((1/2:ℂ))) := by
  have h := nativeFirstOddJetTailScale_mul_greenStep_tendsto
  have hstar := (continuous_star.tendsto _).comp h
  have hprod := hstar.mul h
  have hlimit :
      star (((Real.sqrt 2 : ℝ)⁻¹ : ℂ)) *
        (((Real.sqrt 2 : ℝ)⁻¹ : ℂ)) = (1/2:ℂ) := by
    have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
    have hsqrt_sq : (Real.sqrt 2)^2 = 2 :=
      Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    have hreal : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1/2:ℝ) := by
      field_simp [hsqrt]
      nlinarith [hsqrt_sq]
    rw [show star (((Real.sqrt 2 : ℝ)⁻¹ : ℂ)) =
      (((Real.sqrt 2 : ℝ)⁻¹ : ℂ)) by simp]
    norm_cast
    simpa using congrArg (fun x : ℝ => (x : ℂ)) hreal
  rw [hlimit] at hprod
  simpa using hprod

/-- Exact transport of the first odd jet Schur form to the raw physical
one-tail Schur form.  The eventual cutoff is only the already established
nonvanishing of the physical head deficit. -/
theorem nativeRawJetSchur_firstOdd_exact_scale :
    ∀ᶠ k : ℕ in atTop,
      nativeRawSchurForm k 1
          (nativeSourceChiralJetInput 1 k nativeFirstOddJetDirection)
          (nativeSourceChiralJetInput 1 k nativeFirstOddJetDirection) =
        star (nativeFirstOddJetTailScale k) * nativeFirstOddJetTailScale k *
          nativeRawSchurForm k 1 (Pi.single 1 (1:ℂ)) (Pi.single 1 (1:ℂ)) := by
  filter_upwards [oneDeficit_eventually_pos] with k hk
  simpa [nativeFirstOddJetTailScale] using
    (nativeRawSchurForm_two_source_tail_scale k (ne_of_gt hk)
      (nativeSourceChiralJetInput 1 k nativeFirstOddJetDirection))

theorem canonicalFirstOddSourceSchur_eq_moment_one :
    sourceMomentSchur canonicalCompletedNativeLogDerivativeMoment 1 0 =
      canonicalCompletedNativeLogDerivativeMoment 1 := by
  simp [sourceMomentSchur, sourceMomentMatrix]

def rawKernelOrderOne (h₀ x y : ℝ) : ℝ := -8*h₀^2*(x+y)

def rawKernelOrderTwo (h₀ h₁ x y : ℝ) : ℝ :=
  16*h₀^3*(x^2+x*y+y^2)-4*h₁*(x^2-x*y+y^2)

def rawSchurOrderTwo (h₀ h₁ : ℝ) (i j : ℕ) : ℝ :=
  rawKernelOrderTwo h₀ h₁ (i+2) (j+2) -
    rawKernelOrderTwo h₀ h₁ 1 (j+2) -
    rawKernelOrderTwo h₀ h₁ (i+2) 1 +
    rawKernelOrderTwo h₀ h₁ 1 1 -
    (rawKernelOrderOne h₀ (i+2) 1-rawKernelOrderOne h₀ 1 1) *
      (rawKernelOrderOne h₀ 1 (j+2)-rawKernelOrderOne h₀ 1 1) /
        (4*h₀)

theorem rawKernelOrderOne_schur_cancels (h₀ : ℝ) (i j : ℕ) :
    rawKernelOrderOne h₀ (i+2) (j+2) -
      rawKernelOrderOne h₀ 1 (j+2) -
      rawKernelOrderOne h₀ (i+2) 1 +
      rawKernelOrderOne h₀ 1 1 = 0 := by
  simp [rawKernelOrderOne]
  ring

theorem rawSchurOrderTwo_eq_first_odd_pivot (h₀ h₁ : ℝ) (i j : ℕ) :
    rawSchurOrderTwo h₀ h₁ i j = 4*h₁*(i+1)*(j+1) := by
  unfold rawSchurOrderTwo rawKernelOrderOne rawKernelOrderTwo
  field_simp
  ring

end
end CarryCauchyResidual
