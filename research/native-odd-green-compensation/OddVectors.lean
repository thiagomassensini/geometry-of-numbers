import CubicRecomposition

namespace CarryOddGreen
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryCommutatorControl CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryMixedParity CarryCrossRadial CarryGreenLeading CarryGreenCubic NativeLaguerre NativeCauchyPorts
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000

/-- Columns of the EXISTING bounded physical Green/resolvent operators. -/
abbrev greenColumn (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) (j : ℕ) :=
  physicalGreenOperator eta h0.le h1 (completedNativeChiralCauchyFeature j)
abbrev traceColumn (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) (j : ℕ) :=
  ((physicalGreenResolvent eta h0.le h1)^2) (completedNativeChiralCauchyFeature j)

/-- The odd input is calibrated to the ORIGINAL radial jet, with its phase. -/
theorem odd_profile_radial_jet (k : ℕ) :
    radialJetCoefficients k 1=((k:ℂ)+1) • nativeOddProfile 0 := by
  simpa only [Nat.mul_zero,zero_add,pow_one] using radial_odd_calibration k 0

/-- The actual finite TFVD bulk, including its outgoing address 2. -/
theorem odd_bulk_coefficients (eta : ℝ) :
    finiteTfvdBulk eta (nativeOddProfile 0)=
      Finsupp.single 1 (Complex.I*(2+(eta:ℂ)))+
      Finsupp.single 2 (-Complex.I*(eta:ℂ)) := by
  rw [odd_profile_zero]
  ext j
  rcases j with _ | _ | _ | j <;>
    simp [finiteTfvdBulk_zero,finiteTfvdBulk_succ] <;> ring

/-- Arithmetic address weighting of the SAME odd input. -/
theorem odd_weighted_coefficients (d : ℕ) :
    coefficientWeight (monomialWeight d) (nativeOddProfile 0)=
      Finsupp.single 0 Complex.I+Finsupp.single 1 (-Complex.I*(2:ℂ)^d) := by
  rw [odd_profile_zero]
  ext j
  rcases j with _ | _ | j <;> simp [coefficient_weight_apply,monomialWeight]
  all_goals ring

/-- All degrees, derived from the ORIGINAL completion commutator. -/
theorem odd_commutator_coefficients (d : ℕ) (eta : ℝ) :
    completionCommutator eta (monomialWeight d) (nativeOddProfile 0)=
      Finsupp.single 1 (Complex.I*(eta:ℂ)*(1-(2:ℂ)^d))+
      Finsupp.single 2 (Complex.I*(eta:ℂ)*((3:ℂ)^d-(2:ℂ)^d)) := by
  rw [odd_profile_zero]
  ext j
  rcases j with _ | _ | _ | j <;>
    simp [completion_commutator_zero,completion_commutator_succ,monomialWeight] <;> ring

/-- Explicit bulk vector before ANY inner product. -/
theorem odd_bulk_vector (d : ℕ) (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    partField eta h0 h1 (monomialWeight d) (nativeOddProfile 0) 0=
      (Complex.I*((2:ℂ)^d*(2+(eta:ℂ)))) • greenColumn eta h0 h1 1+
      (-Complex.I*(eta:ℂ)*(3:ℂ)^d) • greenColumn eta h0 h1 2 := by
  have hw : coefficientWeight (monomialWeight d) (finiteTfvdBulk eta (nativeOddProfile 0))=
      Finsupp.single 1 (Complex.I*((2:ℂ)^d*(2+(eta:ℂ))))+
      Finsupp.single 2 (-Complex.I*(eta:ℂ)*(3:ℂ)^d) := by
    rw [odd_bulk_coefficients]
    ext j
    rcases j with _ | _ | _ | j <;> simp [coefficient_weight_apply,monomialWeight] <;> ring
  change physicalGreenOperator eta h0.le h1
    (physicalCauchySynthesis (coefficientWeight (monomialWeight d) (finiteTfvdBulk eta (nativeOddProfile 0))))=_
  rw [hw]
  simp only [map_add,physicalCauchySynthesis,Finsupp.linearCombination_single,map_smul,greenColumn]

/-- BOTH boundary coordinates remain, including the -2 eta central term. -/
theorem odd_boundary_vector (d : ℕ) (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    partField eta h0 h1 (monomialWeight d) (nativeOddProfile 0) 1=
      Complex.I • (traceColumn eta h0 h1 0-
        ((2:ℂ)^d+2*(eta:ℂ)) • traceColumn eta h0 h1 1) := by
  change ((physicalGreenResolvent eta h0.le h1)^2)
    ((monomialWeight d 0*nativeOddProfile 0 0) • completedNativeChiralCauchyFeature 0+
      (monomialWeight d 1*nativeOddProfile 0 1-2*(eta:ℂ)*(monomialWeight d 0*nativeOddProfile 0 0)) •
        completedNativeChiralCauchyFeature 1)=_
  rw [odd_profile_zero]
  simp only [Finsupp.add_apply,Finsupp.single_eq_same,Finsupp.single_eq_of_ne (by decide : (1:ℕ)≠0),
    Finsupp.single_eq_of_ne (by decide : (0:ℕ)≠1),add_zero,zero_add,monomialWeight]
  norm_num only [Nat.zero_add,Nat.cast_one,Nat.reduceAdd,Nat.cast_ofNat,one_mul]
  simp only [map_add,map_smul,traceColumn]
  module

/-- The recommended odd complement formula in the original physical domain. -/
theorem odd_residual_vector (d : ℕ) (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    partField eta h0 h1 (monomialWeight d) (nativeOddProfile 0) 2=
      (Complex.I*(eta:ℂ)) •
        ((1-(2:ℂ)^d) • greenColumn eta h0 h1 1+
         ((3:ℂ)^d-(2:ℂ)^d) • greenColumn eta h0 h1 2) := by
  change physicalGreenOperator eta h0.le h1
    (physicalCauchySynthesis (completionCommutator eta (monomialWeight d) (nativeOddProfile 0)))=_
  rw [odd_commutator_coefficients]
  simp only [map_add,physicalCauchySynthesis,Finsupp.linearCombination_single,map_smul,greenColumn]
  module

end
end CarryOddGreen
