import OddWeights

namespace CarryCubicOdd
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryCommutatorControl CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryMixedParity CarryCrossRadial CarryGreenLeading CarryGreenCubic CarryOddGreen NativeLaguerre NativeCauchyPorts
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000

/-- The ORIGINAL cubic odd profile, including factorial and imaginary phase. -/
theorem cubic_odd_profile : nativeOddProfile 1=
    Finsupp.single 0 (-Complex.I/6)+Finsupp.single 1 (Complex.I/2)+
    Finsupp.single 2 (-Complex.I/2)+Finsupp.single 3 (Complex.I/6) := by
  ext j
  rcases j with _ | _ | _ | _ | j
  all_goals norm_num [nativeOddProfile,staticStencil,raw_stencil_apply,completedGreenForwardWeight]
  all_goals try ring
  simp [Finsupp.single_eq_of_ne (by omega : 4+j≠2),
    Finsupp.single_eq_of_ne (by omega : 4+j≠3)]

/-- The outgoing material address 4 is retained in the native TFVD bulk. -/
theorem cubic_bulk_coefficients (eta : ℝ) :
    finiteTfvdBulk eta (nativeOddProfile 1)=
      Finsupp.single 1 ((Complex.I/6)*(-3*(eta:ℂ)⁻¹-6-(eta:ℂ)))+
      Finsupp.single 2 ((Complex.I/6)*((eta:ℂ)⁻¹+6+3*(eta:ℂ)))+
      Finsupp.single 3 ((Complex.I/6)*(-2-3*(eta:ℂ)))+
      Finsupp.single 4 ((Complex.I/6)*(eta:ℂ)) := by
  rw [cubic_odd_profile]
  ext j
  rcases j with _ | _ | _ | _ | _ | j <;>
    simp [finiteTfvdBulk_zero,finiteTfvdBulk_succ] <;> ring

theorem cubic_weighted_input (w : ℕ → ℂ) :
    coefficientWeight w (nativeOddProfile 1)=
      Finsupp.single 0 ((Complex.I/6)*(-w 0))+
      Finsupp.single 1 ((Complex.I/6)*(3*w 1))+
      Finsupp.single 2 ((Complex.I/6)*(-3*w 2))+
      Finsupp.single 3 ((Complex.I/6)*w 3) := by
  rw [cubic_odd_profile]
  ext j
  rcases j with _ | _ | _ | _ | j <;> simp [coefficient_weight_apply] <;> ring

theorem cubic_commutator_coefficients (w : ℕ → ℂ) (eta : ℝ) :
    completionCommutator eta w (nativeOddProfile 1)=
      Finsupp.single 1 ((Complex.I/6)*(-3*(eta:ℂ)⁻¹*(w 2-w 1)-(eta:ℂ)*(w 0-w 1)))+
      Finsupp.single 2 ((Complex.I/6)*((eta:ℂ)⁻¹*(w 3-w 2)+3*(eta:ℂ)*(w 1-w 2)))+
      Finsupp.single 3 ((Complex.I/6)*(-3*(eta:ℂ)*(w 2-w 3)))+
      Finsupp.single 4 ((Complex.I/6)*((eta:ℂ)*(w 3-w 4))) := by
  rw [cubic_odd_profile]
  ext j
  rcases j with _ | _ | _ | _ | _ | j <;>
    simp [completion_commutator_zero,completion_commutator_succ] <;> ring

theorem cubic_bulk_vector (w : ℕ → ℂ) (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    partField eta h0 h1 w (nativeOddProfile 1) 0=
      (Complex.I/6) •
        ((w 1*(-3*(eta:ℂ)⁻¹-6-(eta:ℂ))) • greenColumn eta h0 h1 1+
         (w 2*((eta:ℂ)⁻¹+6+3*(eta:ℂ))) • greenColumn eta h0 h1 2+
         (w 3*(-2-3*(eta:ℂ))) • greenColumn eta h0 h1 3+
         (w 4*(eta:ℂ)) • greenColumn eta h0 h1 4) := by
  have hw : coefficientWeight w (finiteTfvdBulk eta (nativeOddProfile 1))=
      Finsupp.single 1 ((Complex.I/6)*(w 1*(-3*(eta:ℂ)⁻¹-6-(eta:ℂ))))+
      Finsupp.single 2 ((Complex.I/6)*(w 2*((eta:ℂ)⁻¹+6+3*(eta:ℂ))))+
      Finsupp.single 3 ((Complex.I/6)*(w 3*(-2-3*(eta:ℂ))))+
      Finsupp.single 4 ((Complex.I/6)*(w 4*(eta:ℂ))) := by
    rw [cubic_bulk_coefficients]
    ext j
    rcases j with _ | _ | _ | _ | _ | j <;> simp [coefficient_weight_apply] <;> ring
  change physicalGreenOperator eta h0.le h1
    (physicalCauchySynthesis (coefficientWeight w (finiteTfvdBulk eta (nativeOddProfile 1))))=_
  rw [hw]
  simp only [map_add,physicalCauchySynthesis,Finsupp.linearCombination_single,map_smul,greenColumn]
  module

/-- Both original boundary coordinates, with their 2 eta correction. -/
theorem cubic_boundary_vector (w : ℕ → ℂ) (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    partField eta h0 h1 w (nativeOddProfile 1) 1=
      (Complex.I/6) •
        ((-w 0) • traceColumn eta h0 h1 0+
         (3*w 1+2*(eta:ℂ)*w 0) • traceColumn eta h0 h1 1) := by
  change ((physicalGreenResolvent eta h0.le h1)^2)
    ((w 0*nativeOddProfile 1 0) • completedNativeChiralCauchyFeature 0+
      (w 1*nativeOddProfile 1 1-2*(eta:ℂ)*(w 0*nativeOddProfile 1 0)) •
        completedNativeChiralCauchyFeature 1)=_
  rw [cubic_odd_profile]
  norm_num only [Finsupp.add_apply,Finsupp.single_apply]
  simp only [ite_true,ite_false,add_zero,zero_add]
  simp only [map_add,map_smul,traceColumn]
  module

theorem cubic_residual_vector (w : ℕ → ℂ) (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    partField eta h0 h1 w (nativeOddProfile 1) 2=
      (Complex.I/6) •
        ((-3*(eta:ℂ)⁻¹*(w 2-w 1)-(eta:ℂ)*(w 0-w 1)) • greenColumn eta h0 h1 1+
         ((eta:ℂ)⁻¹*(w 3-w 2)+3*(eta:ℂ)*(w 1-w 2)) • greenColumn eta h0 h1 2+
         (-3*(eta:ℂ)*(w 2-w 3)) • greenColumn eta h0 h1 3+
         ((eta:ℂ)*(w 3-w 4)) • greenColumn eta h0 h1 4) := by
  change physicalGreenOperator eta h0.le h1
    (physicalCauchySynthesis (completionCommutator eta w (nativeOddProfile 1)))=_
  rw [cubic_commutator_coefficients]
  simp only [map_add,physicalCauchySynthesis,Finsupp.linearCombination_single,map_smul,greenColumn]
  module

/-- The w(4) halo cancels between bulk and residual, BEFORE pairing. -/
theorem cubic_bulk_residual_cancellation (w : ℕ → ℂ) (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    partField eta h0 h1 w (nativeOddProfile 1) 0+
      partField eta h0 h1 w (nativeOddProfile 1) 2=
      (Complex.I/6) •
        ((-3*(eta:ℂ)⁻¹*w 2-6*w 1-(eta:ℂ)*w 0) • greenColumn eta h0 h1 1+
         ((eta:ℂ)⁻¹*w 3+6*w 2+3*(eta:ℂ)*w 1) • greenColumn eta h0 h1 2+
         (-2*w 3-3*(eta:ℂ)*w 2) • greenColumn eta h0 h1 3+
         ((eta:ℂ)*w 3) • greenColumn eta h0 h1 4) := by
  rw [cubic_bulk_vector,cubic_residual_vector]
  module

/-- Full synthesis, keeping the true four-address source and its phase. -/
theorem cubic_complete_vector (w : ℕ → ℂ) (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    (∑ a : Fin 3, partField eta h0 h1 w (nativeOddProfile 1) a)=
      (Complex.I/6) •
        ((-w 0) • completedNativeChiralCauchyFeature 0+
         (3*w 1) • completedNativeChiralCauchyFeature 1+
         (-3*w 2) • completedNativeChiralCauchyFeature 2+
         w 3 • completedNativeChiralCauchyFeature 3) := by
  rw [part_field_reconstruction,cubic_weighted_input]
  simp only [map_add,physicalCauchySynthesis,Finsupp.linearCombination_single]
  module

end
end CarryCubicOdd
