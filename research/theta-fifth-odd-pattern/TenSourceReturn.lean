import FifthOddCertificate
import PolarizedCritical

/-! Fixed-dimension parity interface and the resulting ten-source return.
All metrics, source transforms and physical limit carriers are inherited. -/
namespace CarryThetaPattern
open CarrySelfAdjointOperator CarrySelfAdjointOperator.ChiralReturn
open CarryCriticalSource CarryCorrectedGreenPorts CarryReturnCompatibility
open GeometryOfNumbers.Analysis CarryMaterialMixedSchurComparison Filter
open scoped BigOperators Matrix ComplexConjugate InnerProductSpace Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

private def crossSector (s n : ℕ) (z : Fin n → ℂ) : ℝ :=
  ∑ i, ∑ j, h (i.val+j.val+s)*(conj (z i)*z j).re

private theorem crossSector_real_imag (s n : ℕ) (z : Fin n → ℂ) :
    crossSector s n z =
      sourceMomentQuadratic h s n (fun i => (z i).re)+
        sourceMomentQuadratic h s n (fun i => (z i).im) := by
  simp only [crossSector,sourceMomentQuadratic,sourceMomentMatrix,dotProduct,
    Matrix.mulVec,Pi.star_apply,star_trivial,Complex.mul_re,Complex.conj_re,
    Complex.conj_im,neg_mul,sub_neg_eq_add,Finset.mul_sum,mul_add,Finset.sum_add_distrib]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;>
    apply Finset.sum_congr rfl <;> intro j _ <;> ring

private theorem crossSector_nonneg (s n : ℕ)
    (hA : (sourceMomentMatrix h s n).PosDef) (z : Fin n → ℂ) :
    0 ≤ crossSector s n z := by
  rw [crossSector_real_imag]
  exact add_nonneg (hA.posSemidef.dotProduct_mulVec_nonneg _)
    (hA.posSemidef.dotProduct_mulVec_nonneg _)

private theorem crossSector_pos (s n : ℕ)
    (hA : (sourceMomentMatrix h s n).PosDef) (z : Fin n → ℂ) (hz : z ≠ 0) :
    0 < crossSector s n z := by
  rw [crossSector_real_imag]
  by_cases hr : (fun i => (z i).re) = 0
  · have hi : (fun i => (z i).im) ≠ 0 := by
      intro hi
      apply hz
      funext i
      apply Complex.ext
      · exact congrFun hr i
      · exact congrFun hi i
    exact add_pos_of_nonneg_of_pos (hA.posSemidef.dotProduct_mulVec_nonneg _)
      (hA.dotProduct_mulVec_pos hi)
  · exact add_pos_of_pos_of_nonneg (hA.dotProduct_mulVec_pos hr)
      (hA.posSemidef.dotProduct_mulVec_nonneg _)

/-- The fixed-n counterpart of the existing all-order Stieltjes gate.
The converse direction reuses PR #27's source-to-matrix extraction. -/
theorem finiteBoundary_positive_iff_sectorMatrices (n : ℕ) :
    (∀ x : Fin (2*n) → ℂ, x ≠ 0 → 0 < nativeSourceFiniteBoundaryEnergy (2*n) x) ↔
      (sourceMomentMatrix h 0 n).PosDef ∧ (sourceMomentMatrix h 1 n).PosDef := by
  constructor
  · intro hb
    exact ⟨sourceMatrix_posDef_of_boundary 0 n hb,sourceMatrix_posDef_of_boundary 1 n hb⟩
  · rintro ⟨hE,hO⟩ x hx
    rw [nativeSourceFiniteBoundaryEnergy_even_split,primeDepthGeometricMoment_eq_canonical]
    change 0 < 4*(crossSector 0 n (nativeSourceEvenBoundaryPhase n x)+
      crossSector 1 n (nativeSourceOddBoundaryPhase n x))
    rcases nativeSourceBoundaryPhase_nonzero n x hx with he|ho
    · exact mul_pos (by norm_num) (add_pos_of_pos_of_nonneg
        (crossSector_pos 0 n hE _ he) (crossSector_nonneg 1 n hO _))
    · exact mul_pos (by norm_num) (add_pos_of_nonneg_of_pos
        (crossSector_nonneg 0 n hE _) (crossSector_pos 1 n hO _ ho))

theorem ten_boundary_positive (x : Fin 10 → ℂ) (hx : x ≠ 0) :
    0 < nativeSourceFiniteBoundaryEnergy 10 x :=
  (finiteBoundary_positive_iff_sectorMatrices 5).mpr
    ⟨even_source_five_posDef,odd_source_five_posDef⟩ x hx

theorem ten_return_eventually_contractive :
    ∀ᶠ k : ℕ in atTop, ‖radialReturnTransfer k 10‖ ≤ 1 := by
  obtain ⟨ε,hε,hb⟩ := (nativeSourceFiniteBoundaryEnergy_pos_iff_margin 10).mp ten_boundary_positive
  exact radialReturnTransfer_even_eventually_norm_le_one_of_boundary_margin 5 ε hε hb

theorem return_contractive_through_ten (N : ℕ) (hN : N ≤ 10) :
    ∀ᶠ k : ℕ in atTop, ‖radialReturnTransfer k N‖ ≤ 1 := by
  filter_upwards [ten_return_eventually_contractive] with k hk
  exact radialReturnTransfer_norm_le_one_of_prefix k hN hk

theorem correctedGreen_ten_physical_realization (eta : ℝ) (heta : eta ≠ 0) :
    ∃ v : Fin 10 → CanonicalCompletedNativeChiralCauchyCarrier,
      (∀ a, v a ∈ RadialIncidentSpan 0 10) ∧
      (∀ a b, inner ℂ (v a) (v b) = carryValveConfluentJet eta a.val b.val) :=
  correctedGreen_realization_of_contractive 9 ten_return_eventually_contractive eta heta

theorem canonical_ten_physical_realization :
    ∃ v : Fin 10 → CanonicalCompletedNativeChiralCauchyCarrier,
      (∀ a, v a ∈ RadialIncidentSpan 0 10) ∧
      (∀ a b, inner ℂ (fullSourceJet v a) (fullSourceJet v b) =
        polarizedGreenMomentCoefficient canonicalCompletedNativeLogDerivativeMoment a.val b.val) := by
  obtain ⟨v,hmem,hv⟩ := correctedGreen_ten_physical_realization 1 (by norm_num)
  refine ⟨v,hmem,?_⟩
  apply fullSourceJet_pairing v
  intro a b
  rw [hv a b,material_valve_confluent_jet 1 (by norm_num)]

theorem ten_nested_physical_realization (eta : ℝ) (heta : eta ≠ 0) :
    ∃ v : Fin 10 → CanonicalCompletedNativeChiralCauchyCarrier,
      ∀ (N : ℕ) (hN : N ≤ 10) (a b : Fin N),
        inner ℂ (v (Fin.castLE hN a)) (v (Fin.castLE hN b)) =
          carryValveConfluentJet eta a.val b.val := by
  obtain ⟨v,_,hv⟩ := correctedGreen_ten_physical_realization eta heta
  exact ⟨v,fun N hN a b => hv (Fin.castLE hN a) (Fin.castLE hN b)⟩

end
end CarryThetaPattern
