import PhysicalJets

namespace CarryConservativeIntertwiner
open CarrySelfAdjointOperator CarrySelfAdjointOperator.NativeLaguerre ChiralReturn
open scoped InnerProductSpace ComplexConjugate BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

theorem original_incident_columns (k N : ℕ) (c : Fin N → ℂ) :
    physicalOriginalIncident k c 1=∑ j,
      (c j*(Real.sqrt ((k:ℝ)+1):ℂ)) • physicalCauchyFeature j := by
  apply Subtype.ext
  simp only [physicalOriginalIncident,Complex.ofReal_one,one_pow,mul_one,
    Submodule.coe_sum,Submodule.coe_smul,physicalCauchyFeature_coe,
    completedNativeRadialChiralCauchyState,smul_smul]

theorem original_returned_columns (k N : ℕ) (c : Fin N → ℂ) :
    physicalOriginalReturned k c 1=∑ j,
      (c j*completedNativeHermiteBiehlerChiralQuotient (canonicalCompletedC3RadialTiltPoint k j)*
        (Real.sqrt ((k:ℝ)+1):ℂ)) • physicalCauchyFeature j := by
  apply Subtype.ext
  simp only [physicalOriginalReturned,Complex.ofReal_one,one_pow,mul_one,
    Submodule.coe_sum,Submodule.coe_smul,physicalCauchyFeature_coe,
    completedNativeRadialChiralMultiplierState,completedNativeRadialChiralCauchyState,smul_smul,mul_assoc]

/-- The actual quotient and all original source coefficients remain explicit. -/
theorem original_transport_defect_columns (R k N : ℕ) (c : Fin N → ℂ) :
    transportDefect R (physicalOriginalIncident k c 1) (physicalOriginalReturned k c 1)=
      ∑ j, (c j*(completedNativeHermiteBiehlerChiralQuotient (canonicalCompletedC3RadialTiltPoint k j)+
        ((rho j)^(R+1):ℂ))*(Real.sqrt ((k:ℝ)+1):ℂ)) • physicalCauchyFeature j := by
  rw [transportDefect,conservativeReturn,neg_apply,original_incident_columns,original_returned_columns,
    map_sum]
  simp only [map_smul,physicalCauchyShift_feature]
  rw [sub_neg_eq_add,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  module

/-- Exact original arithmetic address encoded by the inherited shift eigenvalue. -/
theorem material_address_from_shift (j : ℕ) :
    (1+rho j)/(2*(1-rho j))=(j:ℝ)+1 := by
  apply (div_eq_iff (mul_ne_zero (by norm_num) (ne_of_gt (sub_pos.mpr (rho_lt_one j))))).mpr
  unfold rho
  have hd : 2*(j:ℝ)+3≠0 := by positivity
  field_simp
  ring

/-- Keep k in the original source argument; it cannot be erased by the shift dictionary. -/
theorem radial_argument_from_shift (k j : ℕ) :
    canonicalCompletedC3RadialTiltPoint k j=
      (((1+rho j)/(2*(1-rho j)):ℝ):ℂ)*canonicalCompletedC3RadialTiltStep k := by
  rw [material_address_from_shift]
  simp only [canonicalCompletedC3RadialTiltPoint,Nat.cast_add,Nat.cast_one,Complex.ofReal_add,
    Complex.ofReal_natCast,Complex.ofReal_one]

end
end CarryConservativeIntertwiner
