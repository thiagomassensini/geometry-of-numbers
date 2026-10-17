import CriticalMargins

/-! Discharge source-critical margins from the already certified infinite
theta integrals. The fifth even test uses ten original incident sources;
we do not assert contraction of that whole ten-source return. -/
namespace CarryCriticalSource
open CarrySelfAdjointOperator CarrySelfAdjointOperator.ChiralReturn
open CarryReturnCompatibility CarryIntegralCertificate
open GeometryOfNumbers.Analysis CarryMaterialSourceFactorComparison
open Filter
open scoped BigOperators Matrix Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

theorem parityCoordinates_injective (s : Fin 2) (m : ℕ) :
    Function.Injective (parityCoordinates s (m := m)) := by
  fin_cases s
  · intro v w hvw
    have he := congrArg (nativeSourceEvenBoundaryPhase m) hvw
    change nativeSourceEvenBoundaryPhase m
        (nativeSourceBoundaryFromParity m (fun i => (v i : ℂ)) 0) =
      nativeSourceEvenBoundaryPhase m
        (nativeSourceBoundaryFromParity m (fun i => (w i : ℂ)) 0) at he
    rw [nativeSourceEvenBoundaryPhase_fromParity, nativeSourceEvenBoundaryPhase_fromParity] at he
    funext i
    simpa using congrArg Complex.re (congrFun he i)
  · intro v w hvw
    have he := congrArg (nativeSourceOddBoundaryPhase m) hvw
    change nativeSourceOddBoundaryPhase m
        (nativeSourceBoundaryFromParity m 0 (fun i => (v i : ℂ))) =
      nativeSourceOddBoundaryPhase m
        (nativeSourceBoundaryFromParity m 0 (fun i => (w i : ℂ))) at he
    rw [nativeSourceOddBoundaryPhase_fromParity, nativeSourceOddBoundaryPhase_fromParity] at he
    funext i
    simpa using congrArg Complex.re (congrFun he i)

theorem parityCoordinates_zero (s : Fin 2) (m : ℕ) :
    parityCoordinates s (0 : Fin m → ℝ) = 0 := by
  unfold parityCoordinates
  split_ifs <;> funext a <;> simp [nativeSourceBoundaryFromParity]

theorem sourceMatrix_posDef_of_boundary (s : Fin 2) (m : ℕ)
    (hb : ∀ x : Fin (2*m) → ℂ, x ≠ 0 → 0 < nativeSourceFiniteBoundaryEnergy (2*m) x) :
    (sourceMomentMatrix h s.val m).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (sourceMomentMatrix_isHermitian h s.val m)
  intro v hv
  have hx : parityCoordinates s v ≠ 0 := by
    intro hz
    exact hv (parityCoordinates_injective s m (hz.trans (parityCoordinates_zero s m).symm))
  have hp := hb (parityCoordinates s v) hx
  rw [parityCoordinates_boundary] at hp
  change 0 < sourceMomentQuadratic h s.val m v
  linarith

theorem sourceMatrix_prefix_posDef (s : Fin 2) {n m : ℕ} (hn : n ≤ m)
    (hm : (sourceMomentMatrix h s.val m).PosDef) :
    (sourceMomentMatrix h s.val n).PosDef := by
  exact hm.submatrix (Fin.castLE_injective hn)

theorem sourceMatrices_through_four_posDef (s : Fin 2) (n : ℕ) (hn : n ≤ 4) :
    (sourceMomentMatrix h s.val n).PosDef := by
  apply sourceMatrix_prefix_posDef s hn
  apply sourceMatrix_posDef_of_boundary s 4
  exact nativeSourceFiniteBoundaryEnergy_eight_pos_iff.mpr eighthSourceDiscriminant_pos

/-- Both parities: all four old source pivots have physical margins. -/
theorem criticalMargins_through_four (s : Fin 2) (n : ℕ) (hn : n < 4) :
    HasCriticalMargin s n := by
  apply (criticalMargin_iff_pivot s n (sourceMatrices_through_four_posDef s n (by omega))).mpr
  exact (sourceMomentMatrix_succ_posDef_iff h s.val n
    (sourceMatrices_through_four_posDef s n (by omega))).mp
      (sourceMatrices_through_four_posDef s (n+1) (by omega))

private theorem even_pivots_four_pos (r : ℕ) (hr : r < 4) :
    0 < carryPairingPivot carryMaterialEvenPairing r := by
  by_cases hh : r < 3
  · exact material_even_pivots_three_pos r hh
  · have he : r = 3 := by omega
    subst r
    exact material_fourth_pivot_pos_integral

/-- Matrix bookkeeping on the already synthesized source observations. -/
def restoredEvenFiveFactor : Matrix (Fin 5) (Fin 5) ℝ :=
  carryPairingBorderFactor (h 0) (fun i : Fin 4 => h (i.val+1)) (carryMaterialEvenCholesky 4)

theorem restoredEvenFiveFactor_identity :
    restoredEvenFiveFactor*restoredEvenFiveFactorᵀ = sourceMomentMatrix h 0 5 := by
  have ha := canonicalCompletedNativeLogDerivativeMoment_zero_pos
  ext i j
  refine Fin.cases ?_ (fun k => ?_) i
  · refine Fin.cases ?_ (fun r => ?_) j
    · exact carryPairingBorderFactor_origin (h 0) ha.le _ _
    · simpa only [restoredEvenFiveFactor, sourceMomentMatrix,
        Fin.val_zero, Fin.val_succ, Nat.zero_add, Nat.add_zero] using
        carryPairingBorderFactor_origin_succ (h 0) ha (fun i : Fin 4 => h (i.val+1))
          (carryMaterialEvenCholesky 4) r
  · refine Fin.cases ?_ (fun r => ?_) j
    · exact carryPairingBorderFactor_succ_origin (h 0) ha _ _ k
    · change (carryPairingBorderFactor (h 0) (fun i : Fin 4 => h (i.val+1))
        (carryMaterialEvenCholesky 4)*
        (carryPairingBorderFactor (h 0) (fun i : Fin 4 => h (i.val+1))
          (carryMaterialEvenCholesky 4))ᵀ) k.succ r.succ = _
      rw [carryPairingBorderFactor_succ_succ (h 0) ha, material_fourth_cholesky_integral]
      change h (k.val+1)*h (r.val+1)/h 0+carryMaterialEvenPairing k r = _
      rw [material_even_pairing_source]
      change _ = h (k.val+1+(r.val+1)+0)
      rw [show k.val+1+(r.val+1)+0 = k.val+r.val+2 by omega]
      ring

theorem restoredEvenFiveFactor_det_pos : 0 < restoredEvenFiveFactor.det := by
  apply carryPairingBorderFactor_det_pos (h 0) canonicalCompletedNativeLogDerivativeMoment_zero_pos
  · intro i j hij
    exact carryPairingCholesky_above carryMaterialEvenPairing 4
      (fun r hr => (even_pivots_four_pos r hr).ne') i j hij
  · intro i
    rw [carryMaterialEvenCholesky, carryPairingCholesky_diagonal carryMaterialEvenPairing 4
      (fun r hr => (even_pivots_four_pos r hr).ne')]
    exact Real.sqrt_pos.mpr (even_pivots_four_pos i i.isLt)

theorem even_source_five_posDef : (sourceMomentMatrix h 0 5).PosDef := by
  let C := restoredEvenFiveFactor
  have hd : IsUnit C.det := isUnit_iff_ne_zero.mpr restoredEvenFiveFactor_det_pos.ne'
  letI := Matrix.invertibleOfIsUnitDet C hd
  have hc := (Matrix.PosDef.one (n := Fin 5) (R := ℝ)).mul_mul_conjTranspose_same
    (Matrix.vecMul_injective_of_invertible C)
  rw [Matrix.mul_one, Matrix.conjTranspose_eq_transpose_of_trivial] at hc
  change (restoredEvenFiveFactor*restoredEvenFiveFactorᵀ).PosDef at hc
  rwa [restoredEvenFiveFactor_identity] at hc

/-- A new physical critical test inside the ten-source return, although
contractivity of that WHOLE return has not been established here. -/
theorem fifth_even_pivot_pos : 0 < sourceMomentSchur h 0 4 := by
  exact (sourceMomentMatrix_succ_posDef_iff h 0 4
    (sourceMatrices_through_four_posDef 0 4 (by omega))).mp even_source_five_posDef

/-- Unconditional physical margin from the original infinite source certificate. -/
theorem fifth_even_criticalMargin : HasCriticalMargin 0 4 :=
  (criticalMargin_iff_pivot 0 4 (sourceMatrices_through_four_posDef 0 4 (by omega))).mpr
    fifth_even_pivot_pos

theorem fifth_even_sourceRemainder_pos : 0 < nativeSourceSchurRemainder 0 4 :=
  (criticalMargin_iff_sourceRemainder 0 4
    (sourceMatrices_through_four_posDef 0 4 (by omega))).mp fifth_even_criticalMargin

/-- The positive pivot itself is a valid eventual threshold; no radial
cutoff value or uniform threshold in the order is asserted. -/
theorem fifth_even_eventually_above_pivot :
    ∀ᶠ k : ℕ in atTop, sourceMomentSchur h 0 4 < criticalBalance 0 4 k :=
  (tendsto_order.mp (criticalBalance_tendsto 0 4
    (sourceMatrices_through_four_posDef 0 4 (by omega)))).1 _ (by
      have hp := fifth_even_pivot_pos
      change sourceMomentSchur h 0 4 < 2*sourceMomentSchur h 0 4
      linarith)

end
end CarryCriticalSource
