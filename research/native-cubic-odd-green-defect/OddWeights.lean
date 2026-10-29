import OddRegressions

namespace CarryCubicOdd
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryCommutatorControl CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryMixedParity CarryCrossRadial CarryGreenLeading CarryGreenCubic CarryOddGreen NativeLaguerre NativeCauchyPorts
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000

/-- Arbitrary complex ADDRESS weights on the original odd input, no new source. -/
theorem odd_weighted_input (w : ℕ → ℂ) :
    coefficientWeight w (nativeOddProfile 0)=
      Finsupp.single 0 (Complex.I*w 0)+Finsupp.single 1 (-Complex.I*w 1) := by
  rw [odd_profile_zero]
  ext j
  rcases j with _ | _ | j <;> simp [coefficient_weight_apply] <;> ring

theorem odd_weight_commutator (w : ℕ → ℂ) (eta : ℝ) :
    completionCommutator eta w (nativeOddProfile 0)=
      Finsupp.single 1 (Complex.I*(eta:ℂ)*(w 0-w 1))+
      Finsupp.single 2 (Complex.I*(eta:ℂ)*(w 2-w 1)) := by
  rw [odd_profile_zero]
  ext j
  rcases j with _ | _ | _ | j <;>
    simp [completion_commutator_zero,completion_commutator_succ] <;> ring

theorem odd_weight_bulk (w : ℕ → ℂ) (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    partField eta h0 h1 w (nativeOddProfile 0) 0=
      (Complex.I*w 1*(2+(eta:ℂ))) • greenColumn eta h0 h1 1+
      (-Complex.I*(eta:ℂ)*w 2) • greenColumn eta h0 h1 2 := by
  have hw : coefficientWeight w (finiteTfvdBulk eta (nativeOddProfile 0))=
      Finsupp.single 1 (Complex.I*w 1*(2+(eta:ℂ)))+
      Finsupp.single 2 (-Complex.I*(eta:ℂ)*w 2) := by
    rw [odd_bulk_coefficients]
    ext j
    rcases j with _ | _ | _ | j <;> simp [coefficient_weight_apply] <;> ring
  change physicalGreenOperator eta h0.le h1
    (physicalCauchySynthesis (coefficientWeight w (finiteTfvdBulk eta (nativeOddProfile 0))))=_
  rw [hw]
  simp only [map_add,physicalCauchySynthesis,Finsupp.linearCombination_single,map_smul,greenColumn]

theorem odd_weight_boundary (w : ℕ → ℂ) (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    partField eta h0 h1 w (nativeOddProfile 0) 1=
      Complex.I • (w 0 • traceColumn eta h0 h1 0-
        (w 1+2*(eta:ℂ)*w 0) • traceColumn eta h0 h1 1) := by
  change ((physicalGreenResolvent eta h0.le h1)^2)
    ((w 0*nativeOddProfile 0 0) • completedNativeChiralCauchyFeature 0+
      (w 1*nativeOddProfile 0 1-2*(eta:ℂ)*(w 0*nativeOddProfile 0 0)) •
        completedNativeChiralCauchyFeature 1)=_
  rw [odd_profile_zero]
  simp only [Finsupp.add_apply,Finsupp.single_eq_same,Finsupp.single_eq_of_ne (by decide : (1:ℕ)≠0),
    Finsupp.single_eq_of_ne (by decide : (0:ℕ)≠1),add_zero,zero_add,map_add,map_smul,traceColumn]
  module

theorem odd_weight_residual (w : ℕ → ℂ) (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    partField eta h0 h1 w (nativeOddProfile 0) 2=
      (Complex.I*(eta:ℂ)) •
        ((w 0-w 1) • greenColumn eta h0 h1 1+
         (w 2-w 1) • greenColumn eta h0 h1 2) := by
  change physicalGreenOperator eta h0.le h1 (physicalCauchySynthesis (completionCommutator eta w (nativeOddProfile 0)))=_
  rw [odd_weight_commutator]
  simp only [map_add,physicalCauchySynthesis,Finsupp.linearCombination_single,map_smul,greenColumn]
  module

theorem odd_weight_complete (w : ℕ → ℂ) (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    (∑ a : Fin 3, partField eta h0 h1 w (nativeOddProfile 0) a)=
      (Complex.I*w 0) • completedNativeChiralCauchyFeature 0+
      (-Complex.I*w 1) • completedNativeChiralCauchyFeature 1 := by
  rw [part_field_reconstruction,odd_weighted_input]
  simp only [map_add,physicalCauchySynthesis,Finsupp.linearCombination_single]

/-- The relative-frequency interaction in the user's note, for any two factors.
This asserts coordinates only; it is not a POVM/native-moment identification. -/
theorem odd_weight_two_defects (x y : ℂ) (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (w : ℕ → ℂ) (hw0 : w 0=1) (hw1 : w 1=x) (hw2 : w 2=x*y) :
    partField eta h0 h1 w (nativeOddProfile 0) 2=
      (Complex.I*(eta:ℂ)) •
        ((1-x) • greenColumn eta h0 h1 1-
         (1-y) • greenColumn eta h0 h1 2+
         ((1-x)*(1-y)) • greenColumn eta h0 h1 2) := by
  rw [odd_weight_residual,hw0,hw1,hw2]
  module

end
end CarryCubicOdd
