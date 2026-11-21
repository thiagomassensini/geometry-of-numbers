import NativeTwoPointSchurSourcePositivity
import CarrySelfAdjointOperator.CompletedNativeTfvdSixSourceChiralDefect

/-!
# Unconditional positivity of the ACTUAL material 6-source TFVD/Green,
# on the first TWO chiral radial directions

There is ALREADY an exact matrix identity in the native CSA:
seededClock TFVD 6-source = (1/2) A* (Gram(incident)-Gram(return)) A.

The previous independent-of-RH theta/cosine low-order curvature proof
gave eventual positivity of the ORIGINAL 2x2 Pick kernel.
This file transports that theorem directly to the ORIGINAL MATERIAL
6-source TFVD/Green kernel, without substituting a moment Gram,
zero measure, ad hoc kernel or an RH hypothesis.

This does NOT solve arbitrary N, and it does not prove a PURE C2 proof
of theta curvature (the base input uses the unconditional theta result).
-/

namespace CarryWheelNativeSignedGate

open CarrySelfAdjointOperator CPFormal.Analytic.Cp
open Filter Topology
open scoped ComplexOrder MatrixOrder

noncomputable section

/-- Explicit original TFVD/Green material positivity on a full 2x2
polarized coefficient family, for any admissible material cutoffs M,
q and finite boundary context S, eventually in the true radial k. -/
theorem nativeC3_material_six_source_two_point_eventually_posSemidef
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) :
    ∀ᶠ k : ℕ in atTop,
      (nativeC3SeededClockTfvdSixSourceRadialSampleMatrix
        M q hqpos.le hq1 S k 2).PosSemidef := by
  have hregular : ∀ᶠ k : ℕ in atTop, ∀ i : Fin 2,
      canonicalCompletedC3RadialTiltPoint k i ∈
        completedNativeHeightDomain ∧
      completedNativeOperatorCharacteristic
        (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 ∧
      completedNativePositiveHermiteBiehlerCoordinate
        (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 := by
    rw [Filter.eventually_all]
    intro i
    exact (canonicalCompletedC3RadialTiltPoint_tendsto_zero i).eventually
      completedNativeChiralPickFactorization_eventually_regular
  filter_upwards
    [canonicalCompletedNativeRadialChiralPickSampleMatrix_two_eventually_posSemidef,
      hregular] with k hkPick hkRegular
  apply
    (nativeC3SeededClockTfvdSixSourceRadialSampleMatrix_posSemidef_iff_chiralMultiplierContractive
      M q hqpos hq1 S k 2 hkRegular).mpr
  exact
    (canonicalCompletedNativeRadialChiralMultiplierContractiveAt_iff_pickPosSemidef
      k 2).mpr hkPick

end
end CarryWheelNativeSignedGate
