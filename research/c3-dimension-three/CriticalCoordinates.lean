import C3Budget256
import IntegralCertificate

namespace CarryC3DimensionThree
open CarryUniformSource CarrySourceBezout CarrySelfAdjointOperator CarryIntegralCertificate Matrix
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 65536

def oldDet (s : ℕ) : ℝ := nativeH s * nativeH (s+2) - (nativeH (s+1))^2

def criticalV0 (s : ℕ) : ℝ :=
  (nativeH (s+1)*nativeH (s+3) - (nativeH (s+2))^2) / oldDet s

def criticalV1 (s : ℕ) : ℝ :=
  (nativeH (s+1)*nativeH (s+2) - nativeH s*nativeH (s+3)) / oldDet s

def sourceZ1 (s : ℕ) : ℝ := criticalV1 s - nativeC 1/nativeC 0

def sourceZ0 (s : ℕ) : ℝ := criticalV0 s - (nativeC 1/nativeC 0)*sourceZ1 s - nativeC 2/nativeC 0

theorem oldDet_nonzero (s : ℕ) (hA : IsUnit (sourceMomentMatrix nativeH s 2)) : oldDet s ≠ 0 := by
  have hdet : (sourceMomentMatrix nativeH s 2).det ≠ 0 :=
    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hA)
  intro hz
  apply hdet
  have he : (sourceMomentMatrix nativeH s 2).det = oldDet s := by
    simp [Matrix.det_fin_two, sourceMomentMatrix, oldDet, Nat.add_comm]
    ring
  rw [he, hz]

theorem critical_vector_explicit (s : ℕ) (hA : IsUnit (sourceMomentMatrix nativeH s 2)) :
    criticalVector nativeH s 2 = ![criticalV0 s,criticalV1 s,1] := by
  let v := criticalVector nativeH s 2
  have hr := criticalVector_mulVec nativeH s 2 hA
  change sourceMomentMatrix nativeH s 3 *ᵥ v = Fin.snoc 0 _ at hr
  have hv2 : v 2 = 1 := rfl
  have h0 := congrFun hr (0:Fin 3)
  have h1 := congrFun hr (1:Fin 3)
  simp [Matrix.mulVec,dotProduct,Fin.sum_univ_succ,sourceMomentMatrix,hv2] at h0 h1
  have hr1 : (Fin.snoc (0 : Fin 2 → ℝ) (sourceMomentSchur nativeH s 2) : Fin 3 → ℝ) (1 : Fin 3) = 0 := by
    change (Fin.snoc (0 : Fin 2 → ℝ) _ : Fin 3 → ℝ) (Fin.castSucc (1 : Fin 2)) = 0
    rw [Fin.snoc_castSucc]
    rfl
  rw [hr1] at h1
  simp only [Nat.add_comm] at h0 h1
  have hd := oldDet_nonzero s hA
  have hv0 : v 0 = criticalV0 s := by
    unfold criticalV0
    apply (eq_div_iff hd).mpr
    unfold oldDet
    linear_combination (nativeH (s+2))*h0 - (nativeH (s+1))*h1
  have hv1 : v 1 = criticalV1 s := by
    unfold criticalV1
    apply (eq_div_iff hd).mpr
    unfold oldDet
    linear_combination (nativeH s)*h1 - (nativeH (s+1))*h0
  ext i
  fin_cases i
  · simpa using hv0
  · simpa using hv1
  · simpa using hv2

theorem critical_source_explicit (s : ℕ) (hA : IsUnit (sourceMomentMatrix nativeH s 2)) :
    monicSourceDirection nativeC nativeH s 2 = ![sourceZ0 s,sourceZ1 s,1] := by
  let z := monicSourceDirection nativeC nativeH s 2
  have hc : nativeC 0 ≠ 0 := completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero
  have ht := sourceDirection_transport nativeC nativeH hc s 2
  have htz : (convolutionMatrix nativeC 3).transpose *ᵥ z =
      nativeC 0 • criticalVector nativeH s 2 := by
    change (convolutionMatrix nativeC 3).transpose *ᵥ (nativeC 0 • sourceDirection nativeC nativeH s 2) = _
    rw [Matrix.mulVec_smul,ht]
  rw [critical_vector_explicit s hA] at htz
  have hz2 : z 2 = 1 := monicSourceDirection_last nativeC nativeH hc s 2
  have h0 := congrFun htz (0:Fin 3)
  have h1 := congrFun htz (1:Fin 3)
  simp [Matrix.mulVec,dotProduct,Fin.sum_univ_succ,convolutionMatrix,hz2] at h0 h1
  have hz1 : z 1 = sourceZ1 s := by
    unfold sourceZ1
    apply (eq_sub_iff_add_eq).2
    field_simp [hc]
    nlinarith [h1]
  have hz0 : z 0 = sourceZ0 s := by
    unfold sourceZ0
    field_simp [hc]
    rw [← hz1]
    nlinarith [h0]
  ext i
  fin_cases i
  · simpa using hz0
  · simpa using hz1
  · simpa using hz2

#print axioms critical_vector_explicit
#print axioms critical_source_explicit
end
end CarryC3DimensionThree
