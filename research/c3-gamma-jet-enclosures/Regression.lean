import SourceProvenance

open CarryC3Gamma CarryTwoEvenJets

/-- Both real quadratures remain in the complex norm; every jet is checked. -/
example : ∀ r : Fin 7,
    ‖sourceJet r.val nativeGamma-gammaReference r‖ ≤ (1/10^18:ℝ) :=
  native_gamma_seven_boxes

example : ‖Complex.Gamma (1/4)-gammaReference 0‖ ≤ (1/10^18:ℝ) := by
  simpa only [sourceJet,iteratedDeriv_zero,Fin.val_zero,Nat.factorial_zero,
    Nat.cast_one,div_one,nativeGamma,CarrySelfAdjointOperator.operatorHeightParameter,
    mul_zero,add_zero,show (1/2:ℂ)/2=1/4 by norm_num] using native_gamma_seven_boxes 0

example : (10^11:ℚ)/10^30+1/10^25+(4^6:ℚ)/10^32 < 1/10^18 := by norm_num

example : (gammaRealReference 1:ℚ) < 0 ∧ 0 < (gammaRealReference 2:ℚ) := by
  decide +kernel
