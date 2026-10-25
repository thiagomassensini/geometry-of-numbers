import CriticalEvenPorts

namespace CarryInteriorGreen
open CarryFirstOddGreen CarryFiniteGreen CarryRadialGreen CarryMeanContrast CarryRadialRefinement CarryPhysicalTrace CarrySelfAdjointOperator
open CarrySelfAdjointOperator.NativeLaguerre CarrySelfAdjointOperator.NativeCauchyPorts
open scoped BigOperators ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

def prefixRegular (k : ℕ) (j : ℕ) : Prop := ∀ i≤j+1,
  completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i)≠0 ∧
  completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i)≠0

/-- All original addresses, including BOTH exceptional boundary cases. -/
theorem residual_basis_all (η : ℝ) (hη : η≠0) (k j : ℕ) (hr : prefixRegular k j) :
    reconstructedResidual 0 η k (basisInput j)=
      (chiralRadialScale k • residualFeature η k j,chiralRadialScale k • residualFeature η k j) := by
  cases j with
  | zero =>
    simpa [basisInput,initialInput,residualFeature,residual_scale_eq,increment,responseIncrement,smul_smul] using
      reconstructed_residual_initial η k (hr 0 (by omega)).1 (hr 0 (by omega)).2
        (hr 1 (by omega)).1 (hr 1 (by omega)).2
  | succ j =>
    cases j with
    | zero =>
      have h := reconstructed_successor η k (by
        intro i hi
        exact hr i (by simp only [Finset.mem_insert,Finset.mem_singleton] at hi; omega))
      simpa only [residualFeature,smul_smul] using h
    | succ j =>
      have h := reconstructed_interior η hη k j (by
        intro i hi
        exact hr i (by simp only [Finset.mem_insert,Finset.mem_singleton] at hi; omega))
      change reconstructedResidual 0 η k (basisInput (j+2))=_
      rw [h]
      apply Prod.ext <;>
        simp only [residualFeature,interiorPort,smul_sub,smul_smul] <;> module

theorem input_basis_expansion (x : ℕ →₀ ℂ) :
    x=∑ j ∈ x.support, x j • basisInput j := by
  classical
  simpa [Finsupp.sum,basisInput,Finsupp.smul_single] using (Finsupp.sum_single x).symm

def finiteResidualFeature (η : ℝ) (k : ℕ) (x : ℕ →₀ ℂ) : PhysicalCauchySpace :=
  ∑ j ∈ x.support, (x j*chiralRadialScale k) • residualFeature η k j

/-- Closed formula for the ENTIRE original reconstructed residual of every
finite complex input. No source component, independent crossing or boundary
trace is discarded. Regularity is only on a finite prefix of its support. -/
theorem finite_residual_closed (η : ℝ) (hη : η≠0) (k : ℕ) (x : ℕ →₀ ℂ)
    (hr : ∀ j∈x.support, prefixRegular k j) :
    reconstructedResidual 0 η k x=(finiteResidualFeature η k x,finiteResidualFeature η k x) := by
  classical
  change residualMap η k x=_
  conv_lhs => rw [input_basis_expansion x,map_sum]
  simp only [map_smul,residual_map_apply]
  have he : (∑ j ∈ x.support, x j • reconstructedResidual 0 η k (basisInput j))=
      ∑ j ∈ x.support, x j •
        (chiralRadialScale k • residualFeature η k j,chiralRadialScale k • residualFeature η k j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [residual_basis_all η hη k j (hr j hj)]
  rw [he]
  apply Prod.ext
  · have hf := map_sum (AddMonoidHom.fst PhysicalCauchySpace PhysicalCauchySpace)
        (fun j => x j • (chiralRadialScale k • residualFeature η k j,
          chiralRadialScale k • residualFeature η k j)) x.support
    change (∑ j ∈ x.support, x j • (chiralRadialScale k • residualFeature η k j,
      chiralRadialScale k • residualFeature η k j)).1=
        ∑ j ∈ x.support, x j • (chiralRadialScale k • residualFeature η k j) at hf
    simpa only [finiteResidualFeature,smul_smul] using hf
  · have hf := map_sum (AddMonoidHom.snd PhysicalCauchySpace PhysicalCauchySpace)
        (fun j => x j • (chiralRadialScale k • residualFeature η k j,
          chiralRadialScale k • residualFeature η k j)) x.support
    change (∑ j ∈ x.support, x j • (chiralRadialScale k • residualFeature η k j,
      chiralRadialScale k • residualFeature η k j)).2=
        ∑ j ∈ x.support, x j • (chiralRadialScale k • residualFeature η k j) at hf
    simpa only [finiteResidualFeature,smul_smul] using hf

/-- Two independent complex inputs and radial grades. Isotropic does not
mean a zero physical residual, and does not erase the mixed sectors. -/
theorem finite_residual_cross_zero (η : ℝ) (hη : η≠0) (k l : ℕ) (x y : ℕ →₀ ℂ)
    (hx : ∀ j∈x.support, prefixRegular k j) (hy : ∀ j∈y.support, prefixRegular l j) :
    physicalForm (reconstructedResidual 0 η k x) (reconstructedResidual 0 η l y)=0 := by
  rw [finite_residual_closed η hη k x hx,finite_residual_closed η hη l y hy]
  simp only [physicalForm,sub_self,mul_zero]

end
end CarryInteriorGreen
