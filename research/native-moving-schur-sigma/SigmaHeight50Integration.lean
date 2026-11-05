import SigmaRHHeightBridge
import RHHeight.Main
import HardyFirstZero.FirstZero
import HardyTenZeros.TenZeros

/-!
# Closed integration of the certified height-50 zeta results

The finite-height RH, exact zero count, first-zero bracket, and nine remaining box results are
imported from the pinned Lean development. This file translates those theorems into the four
propositions consumed by `SigmaRHHeightBridge`, then closes the isolation and existing Padé
recovery theorems without additional hypotheses.
-/

namespace CarrySigmaObstruction

private theorem height50_rh_certificate : sigmaRHHeight50 := by
  simpa [sigmaRHHeight50, RHHeight.RHHeight50, RHHeight.RHUpToHeight] using
    RHHeight.rh_height_fifty

private theorem height50_count_certificate : sigmaZeroCount50 := by
  simpa [sigmaZeroCount50, sigmaRHStripZerosUpTo, RHHeight.ZeroCountUpTo,
    RHHeight.stripZerosUpTo] using RHHeight.zero_count_fifty

private theorem height50_first_zero_certificate : sigmaFirstZeroBracket := by
  obtain ⟨t, ht, hzero⟩ := HardyFirstZero.first_zero_on_line
  rcases ht with ⟨htlo, htupper⟩
  refine ⟨t, ⟨htlo, ?_⟩, ?_⟩
  · calc
      t < 707 / 50 := htupper
      _ = 1414 / 100 := by norm_num
  · simpa [Complex.I] using hzero

private theorem height50_nine_box_certificates : sigmaNineZeroBoxes := by
  obtain ⟨t1, ht1, hz1⟩ := HardyTenZeros.zero_in_2102
  obtain ⟨t2, ht2, hz2⟩ := HardyTenZeros.zero_in_2501
  obtain ⟨t3, ht3, hz3⟩ := HardyTenZeros.zero_in_3042
  obtain ⟨t4, ht4, hz4⟩ := HardyTenZeros.zero_in_3293
  obtain ⟨t5, ht5, hz5⟩ := HardyTenZeros.zero_in_3758
  obtain ⟨t6, ht6, hz6⟩ := HardyTenZeros.zero_in_4091
  obtain ⟨t7, ht7, hz7⟩ := HardyTenZeros.zero_in_4332
  obtain ⟨t8, ht8, hz8⟩ := HardyTenZeros.zero_in_4800
  obtain ⟨t9, ht9, hz9⟩ := HardyTenZeros.zero_in_4977
  refine ⟨![t1, t2, t3, t4, t5, t6, t7, t8, t9], ?_⟩
  intro i
  fin_cases i
  all_goals
    simp only [sigmaTenZeroBoxLower, sigmaTenZeroBoxUpper, Fin.succ, Fin.zero_eta,
      Matrix.cons_val_zero]
  · exact ⟨ht1, by simpa [Complex.I] using hz1⟩
  · exact ⟨ht2, by simpa [Complex.I] using hz2⟩
  · exact ⟨ht3, by simpa [Complex.I] using hz3⟩
  · exact ⟨ht4, by simpa [Complex.I] using hz4⟩
  · exact ⟨ht5, by simpa [Complex.I] using hz5⟩
  · exact ⟨ht6, by simpa [Complex.I] using hz6⟩
  · exact ⟨ht7, by simpa [Complex.I] using hz7⟩
  · exact ⟨ht8, by simpa [Complex.I] using hz8⟩
  · exact ⟨ht9, by simpa [Complex.I] using hz9⟩

/-- The native sigma isolation theorem with all finite-height premises discharged by the
independently compiled Lean height-50 certificate. -/
theorem exists_firstSigmaDisplacedProductIsolation_from_height50_certificate :
    ∃ γ : ℝ, γ ∈ Set.Ioo (1413 / 100 : ℝ) (1414 / 100) ∧
      SigmaDisplacedProductIsolation (1 / 5) γ (Real.sqrt 300) 1 :=
  exists_firstSigmaDisplacedProductIsolation_from_height50 height50_rh_certificate
    height50_count_certificate height50_first_zero_certificate height50_nine_box_certificates

/-- The same closed certificate feeds the existing Padé recovery theorem. -/
theorem exists_firstSigmaHeight50PadeRecovery_from_certificate :
    ∃ γ : ℝ, γ ∈ Set.Ioo (1413 / 100 : ℝ) (1414 / 100) ∧
      SigmaPadeRootRecovery (1 / 5) γ 1 :=
  exists_firstSigmaHeight50PadeRecovery height50_rh_certificate height50_count_certificate
    height50_first_zero_certificate height50_nine_box_certificates

#print axioms RHHeight.rh_height_fifty
#print axioms RHHeight.zero_count_fifty
#print axioms RHHeight.rh_up_to_height_fiftytwo
#print axioms HardyFirstZero.first_zero_on_line
#print axioms HardyTenZeros.ten_zeros_on_line_below_fifty
#print axioms HardyTenZeros.zero_in_2102
#print axioms HardyTenZeros.zero_in_2501
#print axioms HardyTenZeros.zero_in_3042
#print axioms HardyTenZeros.zero_in_3293
#print axioms HardyTenZeros.zero_in_3758
#print axioms HardyTenZeros.zero_in_4091
#print axioms HardyTenZeros.zero_in_4332
#print axioms HardyTenZeros.zero_in_4800
#print axioms HardyTenZeros.zero_in_4977
#print axioms exists_firstSigmaDisplacedProductIsolation_from_height50_certificate
#print axioms exists_firstSigmaHeight50PadeRecovery_from_certificate

end CarrySigmaObstruction
