import TenScaledBoxes

namespace CarryDirectAnchor
open CarrySelfAdjointOperator CarryCriticalSource CarryCriticalRadialMargin CarryIntegralCertificate CarryVariationalSchur
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 48000000
set_option maxRecDepth 65536
attribute [local irreducible] Box.Mem

def scaledDetBox : Box :=
  ((((Box.point 0).add ((entryBox 0 0).mul (adjBox 0 0))).add
    ((entryBox 0 1).mul (adjBox 1 0))).add
    ((entryBox 0 2).mul (adjBox 2 0))).add ((entryBox 0 3).mul (adjBox 3 0))

theorem scaled_det_box_mem : scaledDetBox.Mem scaledMatrix.det := by
  have h := mem_add (mem_add (mem_add (mem_add (mem_point 0)
    (mem_mul (entry_box_mem 0 0) (adj_box_mem 0 0)))
    (mem_mul (entry_box_mem 0 1) (adj_box_mem 1 0)))
    (mem_mul (entry_box_mem 0 2) (adj_box_mem 2 0)))
    (mem_mul (entry_box_mem 0 3) (adj_box_mem 3 0))
  have he := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 0) (Matrix.mul_adjugate scaledMatrix)
  simp [Matrix.mul_apply,Fin.sum_univ_succ] at he
  have he' : 0+scaledMatrix 0 0*scaledMatrix.adjugate 0 0+
      scaledMatrix 0 1*scaledMatrix.adjugate 1 0+
      scaledMatrix 0 2*scaledMatrix.adjugate 2 0+
      scaledMatrix 0 3*scaledMatrix.adjugate 3 0=scaledMatrix.det := by linarith [he]
  rw [← he']
  simpa only [scaledDetBox,Int.cast_zero] using h

def residualBoxAt (i : ℕ) : Box := if h : i<4 then residualBox ⟨i,h⟩ else Box.all
def adjBoxAt (i j : ℕ) : Box := if hi : i<4 then if hj : j<4 then adjBox ⟨i,hi⟩ ⟨j,hj⟩ else Box.all else Box.all
def residualAt (i : ℕ) : ℝ := if h : i<4 then scaledResidual ⟨i,h⟩ else 0
def adjAt (i j : ℕ) : ℝ := if hi : i<4 then if hj : j<4 then scaledMatrix.adjugate ⟨i,hi⟩ ⟨j,hj⟩ else 0 else 0

def numeratorBox : Box := Box.sum (fun i => Box.sum (fun j =>
  ((residualBoxAt i).mul (residualBoxAt j)).mul (adjBoxAt i j)) 4) 4

def numerator : ℝ := ∑ i ∈ Finset.range 4, ∑ j ∈ Finset.range 4,
  residualAt i*residualAt j*adjAt i j

theorem numerator_box_mem : numeratorBox.Mem numerator := by
  have h := mem_sum (fun i => Box.sum (fun j =>
    ((residualBoxAt i).mul (residualBoxAt j)).mul (adjBoxAt i j)) 4)
    (fun i => ∑ j ∈ Finset.range 4, residualAt i*residualAt j*adjAt i j) 4
    (by
      intro i hi
      apply mem_sum
      intro j hj
      have hri := residual_box_mem ⟨i,hi⟩
      have hrj := residual_box_mem ⟨j,hj⟩
      have ha := adj_box_mem ⟨i,hi⟩ ⟨j,hj⟩
      simp only [residualBoxAt,adjBoxAt,residualAt,adjAt,dif_pos hi,dif_pos hj]
      exact mem_mul (mem_mul hri hrj) ha)
  exact h

def correctionBox : Box := numeratorBox.div scaledDetBox

theorem scaled_det_positive : 0 < scaledMatrix.det := by
  have h := mem_of_contained scaled_det_box_mem
    (show scaledDetBox.contained (.finite (700*intervalScale) (1200*intervalScale))=true by decide +kernel)
  norm_num [Box.Mem,intervalScale] at h
  linarith [h.1]

theorem numerator_eq_dot : numerator = scaledResidual ⬝ᵥ (scaledMatrix.adjugate *ᵥ scaledResidual) := by
  unfold numerator
  simp only [Matrix.mulVec, dotProduct,Finset.mul_sum,← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp [residualAt,adjAt]
  ring

theorem correction_box_mem : correctionBox.Mem
    (scaledResidual ⬝ᵥ (scaledMatrix⁻¹ *ᵥ scaledResidual)) := by
  have h := mem_div numerator_box_mem scaled_det_box_mem
  convert h using 1
  · rfl
  · rw [numerator_eq_dot,Matrix.inv_def,Ring.inverse_eq_inv,Matrix.smul_mulVec,dotProduct_smul]
    simp [smul_eq_mul,div_eq_mul_inv,mul_comm]

/-- Exact enclosure of the inverse residual correction, using ALL sixteen
entries of the diagonally transformed original old block. -/
theorem scaled_inverse_correction_upper :
    scaledResidual ⬝ᵥ (scaledMatrix⁻¹ *ᵥ scaledResidual) < 5/(10:ℝ)^35 := by
  have h := mem_of_contained correction_box_mem
    (show correctionBox.contained (.finite (-(4*10^25)) (4*10^25))=true by decide +kernel)
  norm_num [Box.Mem,intervalScale] at h
  norm_num at *
  linarith [h.2]

end
end CarryDirectAnchor
