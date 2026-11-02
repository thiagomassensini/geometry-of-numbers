import SourceProductRule
import NativeRepartition64

namespace CarrySourceBezout
open scoped BigOperators
noncomputable section

variable {R : Type*} [CommRing R] [IsDomain R]

omit [IsDomain R] in
@[simp] theorem sourceKernelSeries_sourceSeries (c : ℕ → R) (b : Bool) :
    sourceKernelSeries b (sourceSeries c) = sourceKernel c b := by
  rfl

section C3

abbrev nativeCComplex : ℕ → ℂ := fun n => (nativeC n : ℂ)

def regroupedHSeries : PowerSeries ℂ := sourceSeries regroupedHead64

def regroupedTSeries : PowerSeries ℂ := sourceSeries regroupedTail64

def regroupedQSeries : PowerSeries ℂ := regroupedTSeries * regroupedHSeries⁻¹

def regroupedUSeries : PowerSeries ℂ := 1 + regroupedQSeries

def nativeSecondEvenDirection : Fin 2 → ℝ := monicSourceDirection nativeC nativeH 0 1

theorem regroupedHead64_c0_ne_zero : regroupedHead64 0 ≠ 0 := by
  have hbound : ‖regroupedHead64 0 - twoEvenReference 0‖ ≤ (2 / 10 ^ 12 : ℝ) :=
    regrouped_head64_four_bound 0
  have href : (2 / 5 : ℝ) < ‖twoEvenReference 0‖ := by
    norm_num [twoEvenReference, twoEvenReferenceReal]
  have htri : ‖twoEvenReference 0‖ ≤ ‖regroupedHead64 0‖ + ‖regroupedHead64 0 - twoEvenReference 0‖ := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (norm_sub_le (regroupedHead64 0) (regroupedHead64 0 - twoEvenReference 0))
  have hnorm_pos : 0 < ‖regroupedHead64 0‖ := by
    linarith
  exact norm_ne_zero_iff.mp (ne_of_gt hnorm_pos)

theorem regroupedHSeries_c0_ne_zero : PowerSeries.constantCoeff regroupedHSeries ≠ 0 := by
  rw [show regroupedHSeries = sourceSeries regroupedHead64 by rfl]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  simp [sourceSeries, regroupedHead64_c0_ne_zero]

theorem regroupedH_add_T_eq_nativeCSeries :
    regroupedHSeries + regroupedTSeries = sourceSeries nativeCComplex := by
  apply PowerSeries.ext
  intro n
  simpa [regroupedHSeries, regroupedTSeries, nativeCComplex, sourceSeries]
    using (regrouped_source n)

theorem regroupedH_mul_U_eq_nativeCSeries :
    regroupedHSeries * regroupedUSeries = sourceSeries nativeCComplex := by
  have hHz : PowerSeries.constantCoeff regroupedHSeries ≠ 0 := regroupedHSeries_c0_ne_zero
  calc
    regroupedHSeries * regroupedUSeries
        = regroupedHSeries * (1 + regroupedQSeries) := by rfl
    _ = regroupedHSeries + regroupedHSeries * regroupedQSeries := by ring
    _ = regroupedHSeries + regroupedTSeries * (regroupedHSeries * regroupedHSeries⁻¹) := by
          simp [regroupedQSeries]
          ring
    _ = regroupedHSeries + regroupedTSeries := by
          rw [PowerSeries.mul_inv_cancel _ hHz]
          ring
    _ = sourceSeries nativeCComplex := regroupedH_add_T_eq_nativeCSeries

theorem coefficientBlock_second_even_multiplicative_rule :
    coefficientBlock (sourceKernel nativeCComplex false) 2 =
      coefficientBlock (left regroupedUSeries * right regroupedUSeries *
        sourceKernelSeries false regroupedHSeries) 2 +
      coefficientBlock (left regroupedHSeries * right regroupedHSeries *
        sourceKernelSeries false regroupedUSeries) 2 := by
  calc
    coefficientBlock (sourceKernel nativeCComplex false) 2
        = coefficientBlock (sourceKernelSeries false (sourceSeries nativeCComplex)) 2 := by
            simp [sourceKernelSeries_sourceSeries]
    _ = coefficientBlock (sourceKernelSeries false (regroupedHSeries * regroupedUSeries)) 2 := by
          rw [regroupedH_mul_U_eq_nativeCSeries]
    _ = coefficientBlock (left regroupedUSeries * right regroupedUSeries *
          sourceKernelSeries false regroupedHSeries) 2 +
        coefficientBlock (left regroupedHSeries * right regroupedHSeries *
          sourceKernelSeries false regroupedUSeries) 2 := by
          simpa using
            (coefficientBlock_sourceKernelSeries_product_rule false regroupedHSeries regroupedUSeries 2)

def secondEvenMultiplicativeHeadContribution : ℂ :=
  complexPair
    (coefficientBlock (left regroupedUSeries * right regroupedUSeries *
      sourceKernelSeries false regroupedHSeries) 2)
    (fun i => (nativeSecondEvenDirection i : ℂ))
    (fun j => (nativeSecondEvenDirection j : ℂ))

def secondEvenMultiplicativeCorrectionContribution : ℂ :=
  complexPair
    (coefficientBlock (left regroupedHSeries * right regroupedHSeries *
      sourceKernelSeries false regroupedUSeries) 2)
    (fun i => (nativeSecondEvenDirection i : ℂ))
    (fun j => (nativeSecondEvenDirection j : ℂ))

theorem secondEvenMultiplicativeEnergySplit :
    complexPair (coefficientBlock (sourceKernel nativeCComplex false) 2)
      (fun i => (nativeSecondEvenDirection i : ℂ))
      (fun j => (nativeSecondEvenDirection j : ℂ)) =
        secondEvenMultiplicativeHeadContribution + secondEvenMultiplicativeCorrectionContribution := by
  have hblock := coefficientBlock_second_even_multiplicative_rule
  unfold secondEvenMultiplicativeHeadContribution secondEvenMultiplicativeCorrectionContribution
  simpa [complexPair_add] using congrArg
    (fun A => complexPair A
      (fun i => (nativeSecondEvenDirection i : ℂ))
      (fun j => (nativeSecondEvenDirection j : ℂ))) hblock

def secondEvenSourceEnergy : ℂ :=
  complexPair (coefficientBlock (sourceKernel nativeCComplex false) 2)
    (fun i => (nativeSecondEvenDirection i : ℂ))
    (fun j => (nativeSecondEvenDirection j : ℂ))

def secondEvenHeadEnergy : ℂ :=
  coefficientPair regroupedHead64 regroupedHead64 false 2
    nativeSecondEvenDirection nativeSecondEvenDirection

theorem secondEvenSourceEnergy_eq_c0_remainder :
    secondEvenSourceEnergy =
      (nativeC 0 * CarrySelfAdjointOperator.nativeSourceSchurRemainder 0 1 : ℝ) := by
  have hmap := sourceKernel_map Complex.ofRealHom nativeC false
  have hblock := congrArg (fun f : BiSeries ℂ => coefficientBlock f 2) hmap
  rw [coefficientBlock_map] at hblock
  change coefficientBlock (sourceKernel nativeCComplex false) 2 = _ at hblock
  have hpair :
      secondEvenSourceEnergy =
        (matrixPair (coefficientBlock (sourceKernel nativeC false) 2)
          nativeSecondEvenDirection nativeSecondEvenDirection : ℂ) := by
    unfold secondEvenSourceEnergy nativeSecondEvenDirection
    rw [hblock, complexPair_real]
  rw [hpair]
  exact congrArg Complex.ofReal
    (native_monicSourceDirection_remainder false 1 native_even_one_isUnit_from_source)

theorem secondEvenSourceEnergy_eq_c0_sq_schur :
    secondEvenSourceEnergy =
      ((nativeC 0) ^ 2 * CarrySelfAdjointOperator.sourceMomentSchur nativeH 0 1 : ℝ) := by
  rw [secondEvenSourceEnergy_eq_c0_remainder,
    CarrySelfAdjointOperator.nativeSourceSchurRemainder_eq]
  ring

theorem secondEvenEnergyDifference_eq_multiplicativeCorrections :
    secondEvenSourceEnergy - secondEvenHeadEnergy =
      (secondEvenMultiplicativeHeadContribution - secondEvenHeadEnergy) +
        secondEvenMultiplicativeCorrectionContribution := by
  unfold secondEvenSourceEnergy secondEvenHeadEnergy
  rw [secondEvenMultiplicativeEnergySplit]
  ring

/-- First independent quantitative obligation for the multiplicative correction. -/
def secondEvenCorrectionQuotientBoundObligation : Prop :=
  ∀ j : Fin 4, ‖PowerSeries.coeff j.val regroupedQSeries‖ < (3 / 10 ^ 15 : ℝ)

/-- Second quantitative obligation needed to close a finite positive margin by multiplicative deviation. -/
def secondEvenMultiplicativeDeviationObligation : Prop :=
  ‖(complexPair (coefficientBlock (sourceKernel nativeCComplex false) 2)
      (fun i => (nativeSecondEvenDirection i : ℂ))
      (fun j => (nativeSecondEvenDirection j : ℂ))) -
    (coefficientPair regroupedHead64 regroupedHead64 false 2
      nativeSecondEvenDirection nativeSecondEvenDirection)‖ < (5 / 10 ^ 15 : ℝ)

theorem secondEvenSourceEnergy_re_pos_of_multiplicativeDeviation
    (hdev : secondEvenMultiplicativeDeviationObligation) :
    0 < secondEvenSourceEnergy.re := by
  let t0 : ℝ := -(2 : ℝ) * nativeC 2 / nativeC 1
  have hz : nativeSecondEvenDirection = twoMonic t0 := by
    simpa [nativeSecondEvenDirection, t0] using
      (native_monic_two_direction native_even_one_isUnit_from_source)
  have hhead : (1 / 10 ^ 8 : ℝ) < secondEvenHeadEnergy.re :=
    by
      unfold secondEvenHeadEnergy
      rw [hz]
      exact native_regrouped64_head_lower t0 native_monic_two_coordinate_bound
  have habs : |(secondEvenSourceEnergy - secondEvenHeadEnergy).re| < (5 / 10 ^ 15 : ℝ) := by
    have hnorm : ‖secondEvenSourceEnergy - secondEvenHeadEnergy‖ < (5 / 10 ^ 15 : ℝ) := by
      simpa [secondEvenMultiplicativeDeviationObligation,
        secondEvenSourceEnergy, secondEvenHeadEnergy] using hdev
    exact (Complex.abs_re_le_norm (secondEvenSourceEnergy - secondEvenHeadEnergy)).trans_lt hnorm
  have hlow : -((5 / 10 ^ 15 : ℝ)) < (secondEvenSourceEnergy - secondEvenHeadEnergy).re :=
    (abs_lt.mp habs).1
  have hre : secondEvenSourceEnergy.re = secondEvenHeadEnergy.re +
      (secondEvenSourceEnergy - secondEvenHeadEnergy).re := by
    simp [Complex.sub_re]
  rw [hre]
  have hdelta : (1 / 10 ^ 8 : ℝ) - (5 / 10 ^ 15 : ℝ) <
      secondEvenHeadEnergy.re + (secondEvenSourceEnergy - secondEvenHeadEnergy).re := by
    linarith
  have hpos : (0 : ℝ) < (1 / 10 ^ 8 : ℝ) - (5 / 10 ^ 15 : ℝ) := by norm_num
  exact hpos.trans hdelta

end C3

end
end CarrySourceBezout
