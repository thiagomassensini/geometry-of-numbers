import SchurTransport

/-!
# Algebraic separation of a finite Schur residual and radial correction

The modified sequences below are controls for an inference about arbitrary
moment functionals. They are not alternative canonical moments or physical
sources. The original source and its signed Green form are not modified.
-/
namespace CarryBinomialGreen
open CarrySelfAdjointOperator CarryPolarizedFour
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

/-- Every finite Schur expression depends only on its exact finite prefix.
This is an algebraic locality statement, with no invertibility premise. -/
theorem source_schur_eq_of_prefix (m m' : ℕ → ℝ) (s n : ℕ)
    (hm : ∀ j : ℕ, j ≤ 2 * n + s → m j = m' j) :
    sourceMomentSchur m s n = sourceMomentSchur m' s n := by
  have hA : sourceMomentMatrix m s n = sourceMomentMatrix m' s n := by
    ext i j
    exact hm _ (by omega)
  have hb : sourceMomentCoupling m s n = sourceMomentCoupling m' s n := by
    ext i
    exact hm _ (by omega)
  unfold sourceMomentSchur
  rw [hA, hb, hm _ (by omega)]

/-- Change only the next coefficient, outside the finite Schur data. -/
def alterFifthMoment (m : ℕ → ℝ) (t : ℝ) (j : ℕ) : ℝ :=
  if j = 5 then m j + t else m j

theorem alter_fifth_prefix (m : ℕ → ℝ) (t : ℝ) (j : ℕ) (hj : j < 5) :
    alterFifthMoment m t j = m j := by
  simp [alterFifthMoment, show j ≠ 5 by omega]

theorem alter_fifth_matrix (m : ℕ → ℝ) (t : ℝ) :
    sourceMomentMatrix (alterFifthMoment m t) 0 2 = sourceMomentMatrix m 0 2 := by
  ext i j
  exact alter_fifth_prefix m t _ (by omega)

theorem alter_fifth_coupling (m : ℕ → ℝ) (t : ℝ) :
    sourceMomentCoupling (alterFifthMoment m t) 0 2 = sourceMomentCoupling m 0 2 := by
  ext i
  exact alter_fifth_prefix m t _ (by omega)

/-- No invertibility or sign premise is needed to preserve the expression. -/
theorem alter_fifth_schur (m : ℕ → ℝ) (t : ℝ) :
    sourceMomentSchur (alterFifthMoment m t) 0 2 = sourceMomentSchur m 0 2 := by
  unfold sourceMomentSchur
  rw [alter_fifth_matrix, alter_fifth_coupling, alter_fifth_prefix m t 4 (by omega)]

/-- The same coefficients of the original algebraic critical direction. -/
theorem alter_fifth_critical_polynomial (m : ℕ → ℝ) (t : ℝ) :
    criticalPolynomial (alterFifthMoment m t) = criticalPolynomial m := by
  unfold criticalPolynomial inverseCoefficients
  rw [alter_fifth_matrix, alter_fifth_coupling]

/-- The first correction of PR88, extended as an algebraic expression in
an arbitrary functional. This is not a positive form or a new physical metric. -/
def momentCorrection (m : ℕ → ℝ) (u v : Fin 3 → ℝ) : ℝ :=
  -crosses u v 0 * m 1 - 20 * crosses u v 1 * m 2 -
  (126 * crosses u v 2 + 14 * crosses u v 3) * m 3 -
  75 * crosses u v 4 * m 4 - 55 * crosses u v 5 * m 5

/-- Exact identification with the already extracted canonical coefficient. -/
theorem moment_correction_canonical (u v : Fin 3 → ℝ) :
    momentCorrection canonicalCompletedNativeLogDerivativeMoment u v = correctionTerm u v := rfl

/-- Two independent arguments: the change is only the highest ordered cross. -/
theorem alter_fifth_correction (m : ℕ → ℝ) (t : ℝ) (u v : Fin 3 → ℝ) :
    momentCorrection (alterFifthMoment m t) u v =
      momentCorrection m u v - 55 * u 2 * v 2 * t := by
  norm_num [momentCorrection, alterFifthMoment, crosses]
  ring

/-- The Schur stays fixed, while the critical correction changes by -55*t.
This statement makes no claim about the canonical source under perturbation. -/
theorem alter_fifth_critical_correction (m : ℕ → ℝ) (t : ℝ) :
    momentCorrection (alterFifthMoment m t)
      (criticalPolynomial (alterFifthMoment m t))
      (criticalPolynomial (alterFifthMoment m t)) =
      momentCorrection m (criticalPolynomial m) (criticalPolynomial m) - 55 * t := by
  rw [alter_fifth_critical_polynomial, alter_fifth_correction]
  simp [criticalPolynomial]

/-- For arbitrary sequences, the correction can be prescribed while the
critical coefficients and the finite Schur expression stay unchanged. -/
theorem arbitrary_correction_with_fixed_schur (m : ℕ → ℝ) (z : ℝ) :
    ∃ m' : ℕ → ℝ,
      sourceMomentSchur m' 0 2 = sourceMomentSchur m 0 2 ∧
      criticalPolynomial m' = criticalPolynomial m ∧
      momentCorrection m' (criticalPolynomial m') (criticalPolynomial m') = z := by
  let t := (momentCorrection m (criticalPolynomial m) (criticalPolynomial m) - z) / 55
  refine ⟨alterFifthMoment m t, alter_fifth_schur m t,
    alter_fifth_critical_polynomial m t, ?_⟩
  rw [alter_fifth_critical_correction]
  dsimp only [t]
  ring

/-- Two positive atoms, used only as an exact control for a generic inference. -/
def twoAtomControl (j : ℕ) : ℝ := 1 + 2 ^ j

theorem two_atom_prefix_det : (sourceMomentMatrix twoAtomControl 0 2).det = 1 := by
  norm_num [sourceMomentMatrix, Matrix.det_fin_two, twoAtomControl]

theorem two_atom_prefix_isUnit : IsUnit (sourceMomentMatrix twoAtomControl 0 2) := by
  apply (sourceMomentMatrix twoAtomControl 0 2).isUnit_iff_isUnit_det.mpr
  rw [two_atom_prefix_det]
  exact isUnit_one

theorem two_atom_inverse_coefficients : inverseCoefficients twoAtomControl = ![-2, 3] := by
  unfold inverseCoefficients
  rw [Matrix.inv_def]
  ext i
  fin_cases i <;> norm_num [sourceMomentMatrix, sourceMomentCoupling, twoAtomControl,
    Matrix.det_fin_two, Matrix.adjugate_fin_two, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ]

theorem two_atom_critical_polynomial : criticalPolynomial twoAtomControl = ![2, -3, 1] := by
  simp [criticalPolynomial, two_atom_inverse_coefficients]

theorem two_atom_schur_zero : sourceMomentSchur twoAtomControl 0 2 = 0 := by
  change twoAtomControl 4 - sourceMomentCoupling twoAtomControl 0 2 ⬝ᵥ
    inverseCoefficients twoAtomControl = 0
  rw [two_atom_inverse_coefficients]
  norm_num [twoAtomControl, sourceMomentCoupling, dotProduct, Fin.sum_univ_succ]

theorem two_atom_correction_positive :
    momentCorrection twoAtomControl (criticalPolynomial twoAtomControl)
      (criticalPolynomial twoAtomControl) = 1353 := by
  rw [two_atom_critical_polynomial]
  have hz : (![2,-3,1] : Fin 3 → ℝ) 2=1 := rfl
  norm_num [momentCorrection, twoAtomControl, crosses, hz]

/-- A positive radial correction does not generically imply a positive Schur.
The witness is not the canonical sequence; this is no no-go for that source. -/
theorem correction_positive_does_not_force_schur_positive :
    ¬ (∀ m : ℕ → ℝ, IsUnit (sourceMomentMatrix m 0 2) →
      0 < momentCorrection m (criticalPolynomial m) (criticalPolynomial m) →
      0 < sourceMomentSchur m 0 2) := by
  intro h
  have hs := h twoAtomControl two_atom_prefix_isUnit
    (by rw [two_atom_correction_positive]; norm_num)
  rw [two_atom_schur_zero] at hs
  exact lt_irrefl 0 hs

end
end CarryBinomialGreen
