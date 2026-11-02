import CriticalCoordinates

namespace CarryC3DimensionThree
open CarryUniformSource CarrySourceBezout CarrySelfAdjointOperator CarryIntegralCertificate Matrix
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 65536

def detBox (s : ℕ) : Box :=
  ((logMomentBox s).mul (logMomentBox (s+2))).add (((logMomentBox (s+1)).pow 2).neg)
def v0Box (s : ℕ) : Box :=
  (((logMomentBox (s+1)).mul (logMomentBox (s+3))).add (((logMomentBox (s+2)).pow 2).neg)).div (detBox s)
def v1Box (s : ℕ) : Box :=
  (((logMomentBox (s+1)).mul (logMomentBox (s+2))).add (((logMomentBox s).mul (logMomentBox (s+3))).neg)).div (detBox s)
def z1Box (s : ℕ) : Box :=
  (v1Box s).add (((characteristicBox 1).div (characteristicBox 0)).neg)
def z0Box (s : ℕ) : Box :=
  ((v0Box s).add ((((characteristicBox 1).div (characteristicBox 0)).mul (z1Box s)).neg)).add
    (((characteristicBox 2).div (characteristicBox 0)).neg)

theorem hMem (n : ℕ) : (logMomentBox n).Mem (nativeH n) :=
  mem_logMomentBox material_theta_integral_input n

theorem cMem (n : ℕ) : (characteristicBox n).Mem (nativeC n) :=
  mem_characteristicBox material_theta_integral_input n

theorem detMem (s : ℕ) : (detBox s).Mem (oldDet s) := by
  unfold detBox oldDet
  simpa only [sub_eq_add_neg] using mem_add (mem_mul (hMem s) (hMem (s+2))) (mem_neg (mem_pow (hMem (s+1)) 2))

theorem v0Mem (s : ℕ) : (v0Box s).Mem (criticalV0 s) := by
  unfold v0Box criticalV0
  simpa only [sub_eq_add_neg] using mem_div (mem_add (mem_mul (hMem (s+1)) (hMem (s+3))) (mem_neg (mem_pow (hMem (s+2)) 2))) (detMem s)

theorem v1Mem (s : ℕ) : (v1Box s).Mem (criticalV1 s) := by
  unfold v1Box criticalV1
  simpa only [sub_eq_add_neg] using mem_div (mem_add (mem_mul (hMem (s+1)) (hMem (s+2))) (mem_neg (mem_mul (hMem s) (hMem (s+3))))) (detMem s)

theorem z1Mem (s : ℕ) : (z1Box s).Mem (sourceZ1 s) := by
  unfold z1Box sourceZ1
  simpa only [sub_eq_add_neg] using mem_add (v1Mem s) (mem_neg (mem_div (cMem 1) (cMem 0)))

theorem z0Mem (s : ℕ) : (z0Box s).Mem (sourceZ0 s) := by
  unfold z0Box sourceZ0
  simpa only [sub_eq_add_neg] using mem_add (mem_add (v0Mem s) (mem_neg (mem_mul (mem_div (cMem 1) (cMem 0)) (z1Mem s)))) (mem_neg (mem_div (cMem 2) (cMem 0)))


theorem oldDet_positive (b : Bool) : 0 < oldDet (if b then 1 else 0) := by
  cases b
  · exact pos_of_mem (detMem 0) (by decide +kernel)
  · exact pos_of_mem (detMem 1) (by decide +kernel)

theorem oldMatrix_isUnit (b : Bool) : IsUnit (sourceMomentMatrix nativeH (if b then 1 else 0) 2) := by
  apply (Matrix.isUnit_iff_isUnit_det _).2
  apply isUnit_iff_ne_zero.2
  have he : (sourceMomentMatrix nativeH (if b then 1 else 0) 2).det = oldDet (if b then 1 else 0) := by
    simp [Matrix.det_fin_two, sourceMomentMatrix, oldDet, Nat.add_comm]
    ring
  rw [he]
  exact ne_of_gt (oldDet_positive b)

theorem z0_range (b : Bool) : 0 ≤ sourceZ0 (if b then 1 else 0) ∧ sourceZ0 (if b then 1 else 0) ≤ 1/100 := by
  have hm : (Box.finite 0 (10^58)).Mem (sourceZ0 (if b then 1 else 0)) := by
    cases b
    · exact mem_of_contained (z0Mem 0) (by decide +kernel)
    · exact mem_of_contained (z0Mem 1) (by decide +kernel)
  simp only [Box.Mem, Int.cast_zero] at hm
  norm_num [intervalScale] at hm
  constructor <;> nlinarith [hm.1, hm.2]

theorem z1_range (b : Bool) : 0 ≤ sourceZ1 (if b then 1 else 0) ∧ sourceZ1 (if b then 1 else 0) ≤ 1/10 := by
  have hm : (Box.finite 0 (10^59)).Mem (sourceZ1 (if b then 1 else 0)) := by
    cases b
    · exact mem_of_contained (z1Mem 0) (by decide +kernel)
    · exact mem_of_contained (z1Mem 1) (by decide +kernel)
  simp only [Box.Mem, Int.cast_zero] at hm
  norm_num [intervalScale] at hm
  constructor <;> nlinarith [hm.1, hm.2]

theorem critical_coordMass_bound (b : Bool) : coordMass (monicSourceDirection nativeC nativeH (if b then 1 else 0) 2) ≤ 2 := by
  rw [critical_source_explicit _ (oldMatrix_isUnit b)]
  have h0 := z0_range b
  have h1 := z1_range b
  simp [coordMass, Fin.sum_univ_succ, abs_of_nonneg h0.1, abs_of_nonneg h1.1]
  linarith

#print axioms oldMatrix_isUnit
#print axioms critical_coordMass_bound

end
end CarryC3DimensionThree
