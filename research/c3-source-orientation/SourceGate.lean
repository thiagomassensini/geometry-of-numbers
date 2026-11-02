import SourceDependency

namespace CarrySourceDimensionThree
open CarrySourceBezout CarrySelfAdjointOperator
open scoped Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000

def evenSourceCeiling (c : ℕ → ℝ) : ℝ :=
  -3*c 1*c 4 - c 2*c 3 -
    sourceCoupling c false 2 ⬝ᵥ ((coefficientBlock (sourceKernel c false) 2)⁻¹ *ᵥ sourceCoupling c false 2)

def oddSourceCeiling (c : ℕ → ℝ) : ℝ :=
  -4*c 1*c 5 - 2*c 2*c 4 + 3*(c 3)^2 -
    sourceCoupling c true 2 ⬝ᵥ ((coefficientBlock (sourceKernel c true) 2)⁻¹ *ᵥ sourceCoupling c true 2)

theorem even_source_schur_coefficient (c : ℕ → ℝ) :
    sourceSchur c false 2 = evenSourceCeiling c - 5*c 0*c 5 := by
  unfold sourceSchur evenSourceCeiling
  have h := even_last_entry c
  change coefficientBlock (sourceKernel c false) (2+1) (Fin.last 2) (Fin.last 2) = _ at h
  rw [h]
  ring

theorem odd_source_schur_coefficient (c : ℕ → ℝ) :
    sourceSchur c true 2 = oddSourceCeiling c - 6*c 0*c 6 := by
  unfold sourceSchur oddSourceCeiling
  have h := odd_last_entry c
  change coefficientBlock (sourceKernel c true) (2+1) (Fin.last 2) (Fin.last 2) = _ at h
  rw [h]
  ring

theorem even_source_sign_iff (c : ℕ → ℝ) (hc : 0 < c 0) :
    0 < sourceSchur c false 2 ↔ c 5 < evenSourceCeiling c/(5*c 0) := by
  rw [even_source_schur_coefficient, lt_div_iff₀ (by positivity : 0 < 5*c 0)]
  constructor <;> intro h <;> nlinarith

theorem odd_source_sign_iff (c : ℕ → ℝ) (hc : 0 < c 0) :
    0 < sourceSchur c true 2 ↔ c 6 < oddSourceCeiling c/(6*c 0) := by
  rw [odd_source_schur_coefficient, lt_div_iff₀ (by positivity : 0 < 6*c 0)]
  constructor <;> intro h <;> nlinarith

#print axioms even_source_schur_coefficient
#print axioms odd_source_schur_coefficient
#print axioms even_source_sign_iff
#print axioms odd_source_sign_iff
theorem native_even_gate (hA : IsUnit (sourceMomentMatrix nativeH 0 2)) :
    0 < sourceMomentSchur nativeH 0 2 ↔
      nativeC 5 < evenSourceCeiling nativeC/(5*nativeC 0) := by
  have he := even_source_sign_iff nativeC native_source_c0_positive_from_boxes
  rw [sourceSchur_eq_scaled nativeC nativeH
    completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero native_source_recurrence false 2 hA] at he
  simpa only [Bool.false_eq_true, if_false,
    mul_pos_iff_of_pos_left (sq_pos_of_pos native_source_c0_positive_from_boxes)] using he

theorem native_odd_gate (hA : IsUnit (sourceMomentMatrix nativeH 1 2)) :
    0 < sourceMomentSchur nativeH 1 2 ↔
      nativeC 6 < oddSourceCeiling nativeC/(6*nativeC 0) := by
  have he := odd_source_sign_iff nativeC native_source_c0_positive_from_boxes
  rw [sourceSchur_eq_scaled nativeC nativeH
    completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero native_source_recurrence true 2 hA] at he
  simpa only [if_true,
    mul_pos_iff_of_pos_left (sq_pos_of_pos native_source_c0_positive_from_boxes)] using he

#print axioms native_even_gate
#print axioms native_odd_gate

end
end CarrySourceDimensionThree
