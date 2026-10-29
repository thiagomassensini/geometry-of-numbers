import GeometryOfNumbers.Analysis.CarryMaterialCompanionGreenTransport

/-! Orthogonal readout reduction in the existing material metric, and its
exact failure to preserve the geometric clock graph domain. No new metric,
source, readout, or operator is defined here. -/
namespace GeometryOfNumbers.Analysis
open BaseTwoCompletion
open scoped InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem carryMaterialReadoutProjection_readout (y : MaterialCarrier) :
    baseTwoCompletedBoundaryHilbertReadout (carryMaterialReadoutProjection y) =
      baseTwoCompletedBoundaryHilbertReadout y := by
  simp [carryMaterialReadoutProjection, carryMaterialReadoutMeanVector,
    baseTwoCompletedBoundaryHilbertReadout_apply]
  ring

theorem carryMaterialReadoutProjection_complement (y : MaterialCarrier) :
    carryMaterialReadoutComplement (carryMaterialReadoutProjection y) = 0 := by
  change carryMaterialReadoutProjection y -
    carryMaterialReadoutProjection (carryMaterialReadoutProjection y) = 0
  have he : carryMaterialReadoutProjection (carryMaterialReadoutProjection y) =
      carryMaterialReadoutProjection y :=
    congrArg (fun z : ℂ => z • carryMaterialReadoutMeanVector)
      (carryMaterialReadoutProjection_readout y)
  rw [he, sub_self]

/-- Full polarized energy; the hidden component is retained before taking a norm. -/
theorem carryMaterialReadout_norm_decomposition (y : MaterialCarrier) :
    ‖y‖^2 = (1/2 : ℝ)*‖baseTwoCompletedBoundaryHilbertReadout y‖^2 +
      ‖carryMaterialReadoutComplement y‖^2 := by
  have h := carryMaterialReadout_pairing y y
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, mul_assoc,
    ← Complex.normSq_eq_conj_mul_self, ← Complex.sq_norm] at h
  have hr := congrArg Complex.re h
  norm_num [← Complex.ofReal_pow] at hr
  exact hr

/-- The ambient minimum is forced by the old metric, without fitting a factor. -/
theorem carryMaterialReadout_minimum (y : MaterialCarrier) :
    (1/2 : ℝ)*‖baseTwoCompletedBoundaryHilbertReadout y‖^2 ≤ ‖y‖^2 := by
  rw [carryMaterialReadout_norm_decomposition]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem carryMaterialReadoutProjection_norm (y : MaterialCarrier) :
    ‖carryMaterialReadoutProjection y‖^2 =
      (1/2 : ℝ)*‖baseTwoCompletedBoundaryHilbertReadout y‖^2 := by
  rw [carryMaterialReadout_norm_decomposition (carryMaterialReadoutProjection y),
    carryMaterialReadoutProjection_readout, carryMaterialReadoutProjection_complement]
  simp only [norm_zero,zero_pow (by decide : 2 ≠ 0),add_zero]

theorem carryMaterialReadout_minimum_eq_iff (y : MaterialCarrier) :
    ‖y‖^2 = (1/2 : ℝ)*‖baseTwoCompletedBoundaryHilbertReadout y‖^2 ↔
      y = carryMaterialReadoutProjection y := by
  rw [carryMaterialReadout_norm_decomposition]
  constructor
  · intro h
    have hz : carryMaterialReadoutComplement y = 0 := by
      have hn : ‖carryMaterialReadoutComplement y‖^2 = 0 := by linarith
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
    have hr := carryMaterialReadout_reconstruct y
    simpa only [hz, add_zero] using hr.symm
  · intro h
    have hz : carryMaterialReadoutComplement y = 0 := by
      conv_lhs => rw [h]
      exact carryMaterialReadoutProjection_complement y
    simp [hz]

/-- The inherited ambient quotient has a unique minimizing representative.
The graph-domain theorem below shows exactly when this representative is physical. -/
theorem carryMaterialReadout_unique_minimum (y z : MaterialCarrier)
    (hread : baseTwoCompletedBoundaryHilbertReadout z = baseTwoCompletedBoundaryHilbertReadout y) :
    ‖carryMaterialReadoutProjection y‖^2 ≤ ‖z‖^2 ∧
      (‖z‖^2 = ‖carryMaterialReadoutProjection y‖^2 ↔ z = carryMaterialReadoutProjection y) := by
  have hp : carryMaterialReadoutProjection z = carryMaterialReadoutProjection y :=
    congrArg (fun w : ℂ => w • carryMaterialReadoutMeanVector) hread
  rw [carryMaterialReadoutProjection_norm, ← hread]
  exact ⟨carryMaterialReadout_minimum z, by
    simpa only [hp] using carryMaterialReadout_minimum_eq_iff z⟩

/-- Adding the hidden component to the readout is an information-preserving encoding. -/
theorem carryMaterialReadout_complete_injective :
    Function.Injective (fun y : MaterialCarrier =>
      (baseTwoCompletedBoundaryHilbertReadout y, carryMaterialReadoutComplement y)) := by
  intro x y h
  have hp : carryMaterialReadoutProjection x = carryMaterialReadoutProjection y := by
    exact congrArg (fun z : ℂ => z • carryMaterialReadoutMeanVector) (congrArg Prod.fst h)
  have hq : carryMaterialReadoutComplement x = carryMaterialReadoutComplement y :=
    congrArg Prod.snd h
  rw [← carryMaterialReadout_reconstruct x, ← carryMaterialReadout_reconstruct y,
    hp, hq]

/-- Every crossing and both quadratures remain in the energy of an arbitrary finite family. -/
theorem carryMaterialReadout_finite_energy {n : ℕ} (c : Fin n → ℂ)
    (y : Fin n → MaterialCarrier) :
    ‖∑ i, c i • y i‖^2 =
      (1/2 : ℝ)*‖∑ i, c i * baseTwoCompletedBoundaryHilbertReadout (y i)‖^2 +
        ‖∑ i, c i • carryMaterialReadoutComplement (y i)‖^2 := by
  simpa only [map_sum,map_smul,smul_eq_mul] using
    carryMaterialReadout_norm_decomposition (∑ i, c i • y i)

/-- Projection has no material interior, so its actual cell-return sum is zero. -/
theorem carryMaterialReadoutProjection_cells (y : MaterialCarrier) :
    completedBoundaryCellReturnCoordinates (carryMaterialReadoutProjection y) = 0 := by
  funext k
  simp [completedBoundaryCellReturnCoordinates, carryMaterialReadoutProjection,
    carryMaterialReadoutMeanVector]

/-- The exact boundary mismatch introduced by the ambient orthogonal projection. -/
theorem carryMaterialReadoutProjection_boundary_defect (y : MaterialCarrier) :
    (carryMaterialReadoutProjection y).snd.snd -
        ∑' k, completedBoundaryCellReturnCoordinates (carryMaterialReadoutProjection y) k =
      baseTwoCompletedBoundaryHilbertReadout y / 2 := by
  rw [carryMaterialReadoutProjection_cells]
  simp [carryMaterialReadoutProjection, carryMaterialReadoutMeanVector]
  ring

/-- This projection is an admissible graph state only for zero readout. -/
theorem carryMaterialReadoutProjection_mem_domain_iff (y : MaterialCarrier) :
    carryMaterialReadoutProjection y ∈ completedBoundaryTransportedClock.domain ↔
      baseTwoCompletedBoundaryHilbertReadout y = 0 := by
  constructor
  · intro h
    have hs := h.1
    rw [carryMaterialReadoutProjection_cells] at hs
    have hz := hs.unique (hasSum_zero : HasSum (0 : ℕ → ℂ) 0)
    have hb : (carryMaterialReadoutProjection y).snd.snd =
        baseTwoCompletedBoundaryHilbertReadout y / 2 := by
      simp [carryMaterialReadoutProjection, carryMaterialReadoutMeanVector, div_eq_mul_inv]
    rw [hb] at hz
    exact (div_eq_zero_iff).mp hz |>.resolve_right (by norm_num)
  · intro h
    have hz : carryMaterialReadoutProjection y = 0 := by
      simp [carryMaterialReadoutProjection, h]
    rw [hz]
    exact completedBoundaryTransportedClock.domain.zero_mem

theorem carryMaterialReadoutComplement_cells (y : MaterialCarrier) :
    completedBoundaryCellReturnCoordinates (carryMaterialReadoutComplement y) =
      completedBoundaryCellReturnCoordinates y := by
  change completedBoundaryCellReturnCoordinates (y-carryMaterialReadoutProjection y) = _
  rw [map_sub, carryMaterialReadoutProjection_cells, sub_zero]

/-- On an actual graph state, the opposite boundary defect remains in the complement. -/
theorem carryMaterialReadoutComplement_boundary_defect (y : MaterialCarrier)
    (hy : y ∈ completedBoundaryTransportedClock.domain) :
    (carryMaterialReadoutComplement y).snd.snd -
        ∑' k, completedBoundaryCellReturnCoordinates (carryMaterialReadoutComplement y) k =
      -baseTwoCompletedBoundaryHilbertReadout y / 2 := by
  rw [carryMaterialReadoutComplement_cells, hy.1.tsum_eq,
    carryMaterialReadoutComplement_apply, baseTwoCompletedBoundaryHilbertReadout_apply]
  change (y.snd.snd-y.fst)/2-y.snd.snd = -(y.fst+y.snd.snd)/2
  ring

/-- The full sum remains physical, although its two orthogonal pieces generally do not. -/
theorem carryMaterialReadoutComplement_mem_domain_iff (y : MaterialCarrier)
    (hy : y ∈ completedBoundaryTransportedClock.domain) :
    carryMaterialReadoutComplement y ∈ completedBoundaryTransportedClock.domain ↔
      baseTwoCompletedBoundaryHilbertReadout y = 0 := by
  constructor
  · intro hq
    apply (carryMaterialReadoutProjection_mem_domain_iff y).mp
    have hp := completedBoundaryTransportedClock.domain.sub_mem hy hq
    have he : y-carryMaterialReadoutComplement y = carryMaterialReadoutProjection y := by
      have hr := carryMaterialReadout_reconstruct y
      exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using hr.symm)
    simpa only [he] using hp
  · intro h
    rw [carryMaterialReadoutComplement_of_readout_zero y h]
    exact hy

/-- The ambient minimum cannot be attained by a physical graph state with nonzero readout. -/
theorem carryMaterialReadout_physical_strict (y : MaterialCarrier)
    (hy : y ∈ completedBoundaryTransportedClock.domain)
    (hr : baseTwoCompletedBoundaryHilbertReadout y ≠ 0) :
    (1/2 : ℝ)*‖baseTwoCompletedBoundaryHilbertReadout y‖^2 < ‖y‖^2 := by
  apply lt_of_le_of_ne (carryMaterialReadout_minimum y)
  intro he
  have hp := (carryMaterialReadout_minimum_eq_iff y).mp he.symm
  have hd : carryMaterialReadoutProjection y ∈ completedBoundaryTransportedClock.domain :=
    hp ▸ hy
  exact hr ((carryMaterialReadoutProjection_mem_domain_iff y).mp hd)

/-- Concrete source specialization: no domain or nonvanishing hypothesis is left open. -/
theorem carryMaterialReadout_source_projection_not_physical :
    carryMaterialReadoutProjection (baseTwoCompletedBoundaryHilbertState 0) ∉
      completedBoundaryTransportedClock.domain := by
  rw [carryMaterialReadoutProjection_mem_domain_iff,
    baseTwoCompletedBoundaryHilbertReadout_eq_signal]
  exact carryMaterial_origin_signal_ne_zero

/-- An injective isometric transport cannot turn this nonphysical representative
into the image of an actual graph-domain state. -/
theorem carryMaterialReadoutProjection_not_isometric_domain
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (U : MaterialCarrier →ₗᵢ[ℂ] E) (y : MaterialCarrier)
    (hr : baseTwoCompletedBoundaryHilbertReadout y ≠ 0) :
    ¬ ∃ z : completedBoundaryTransportedClock.domain,
      U z.val = U (carryMaterialReadoutProjection y) := by
  rintro ⟨z,hz⟩
  have he := U.injective hz
  have hp : carryMaterialReadoutProjection y ∈ completedBoundaryTransportedClock.domain :=
    he ▸ z.property
  exact hr ((carryMaterialReadoutProjection_mem_domain_iff y).mp hp)

end
end GeometryOfNumbers.Analysis
