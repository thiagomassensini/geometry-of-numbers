import CriticalOddDefect

namespace CarryOddCauchy
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryCommutatorControl CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryMixedParity CarryCrossRadial CarryGreenLeading CarryGreenCubic CarryOddGreen CarryCubicOdd CarryCurvatureGreen NativeLaguerre NativeCauchyPorts
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000

/-- A coordinate of the EXISTING physical complement, not a new operator. -/
abbrev complementRow (m j : ℕ) : ℂ :=
  inner ℂ (completedNativeChiralCauchyFeature j)
    ((physicalComplement^m) (completedNativeChiralCauchyFeature 0))

/-- Transport of the whole physical vector precedes the scalar recurrence. -/
theorem complement_vector_succ (m : ℕ) :
    (physicalComplement^(m+1)) (completedNativeChiralCauchyFeature 0)=
      (physicalComplement^m) (completedNativeChiralCauchyFeature 0)-
      physicalRadialAdvance ((physicalComplement^m) (completedNativeChiralCauchyFeature 0)) := by
  rw [pow_succ',mul_apply_eq_comp]
  simp only [physicalComplement,sub_apply,one_apply_eq_self]

/-- The recurrence follows from the ORIGINAL real multiplier's symmetry.
No canonical moment or positivity assumption enters. -/
theorem complement_row_succ (m j : ℕ) :
    complementRow (m+1) j=complementRow m j-complementRow m (j+1) := by
  unfold complementRow
  rw [complement_vector_succ,inner_sub_right]
  have hs := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    physicalRadialAdvance_isSelfAdjoint)
      (completedNativeChiralCauchyFeature j)
      ((physicalComplement^m) (completedNativeChiralCauchyFeature 0))
  have hs' : inner ℂ (physicalRadialAdvance (completedNativeChiralCauchyFeature j))
      ((physicalComplement^m) (completedNativeChiralCauchyFeature 0))=
      inner ℂ (completedNativeChiralCauchyFeature j)
        (physicalRadialAdvance ((physicalComplement^m) (completedNativeChiralCauchyFeature 0))) := hs
  rw [← hs',physicalRadialAdvance_feature]

theorem complement_row_zero (j : ℕ) :
    complementRow 0 j=(((j+2:ℕ):ℂ))⁻¹ := by
  simp [complementRow,inner_completedNativeChiralCauchyFeature]

theorem factorial_row_zero (j : ℕ) :
    (((j+2:ℕ):ℂ))⁻¹=((j+1).factorial:ℂ)/((j+2).factorial:ℂ) := by
  rw [show j+2=(j+1)+1 by omega,Nat.factorial_succ (j+1)]
  have hf : ((j+1).factorial:ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero (j+1)
  have hn : (j:ℂ)+1+1≠0 := by exact_mod_cast (by omega : j+1+1≠0)
  push_cast
  field_simp

theorem factorial_row_difference (m j : ℕ) :
    (m.factorial:ℂ)*((j+1).factorial:ℂ)/((j+m+2).factorial:ℂ)-
      (m.factorial:ℂ)*((j+1+1).factorial:ℂ)/((j+1+m+2).factorial:ℂ)=
      ((m+1).factorial:ℂ)*((j+1).factorial:ℂ)/((j+(m+1)+2).factorial:ℂ) := by
  rw [show j+1+m+2=(j+m+2)+1 by omega,
    show j+(m+1)+2=(j+m+2)+1 by omega]
  simp only [Nat.factorial_succ (j+m+2),Nat.factorial_succ (j+1),Nat.factorial_succ m]
  have hf : ((j+m+2).factorial:ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero (j+m+2)
  have hn : ((j+m+2+1:ℕ):ℂ)≠0 := by exact_mod_cast (by omega : j+m+2+1≠0)
  push_cast at hn ⊢
  field_simp
  ring

/-- Exact all-order Cauchy coordinate of the original complement powers. -/
theorem complement_row_factorial (m j : ℕ) :
    complementRow m j=(m.factorial:ℂ)*((j+1).factorial:ℂ)/((j+m+2).factorial:ℂ) := by
  induction m generalizing j with
  | zero => simpa only [Nat.factorial_zero,Nat.cast_one,one_mul,Nat.add_zero] using
      (complement_row_zero j).trans (factorial_row_zero j)
  | succ m ih =>
    rw [complement_row_succ,ih,ih,factorial_row_difference]

end
end CarryOddCauchy
