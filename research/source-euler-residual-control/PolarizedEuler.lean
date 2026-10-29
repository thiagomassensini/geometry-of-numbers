import ResidualEuler

/-! Two independent complete source inputs, BEFORE any diagonal energy test. -/
namespace CarryResidualEuler
open CarrySelfAdjointOperator ChiralReturn CarryJetOverlap CarryFiberTransport
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- Both ordered mixed pairings of the existing nonlinear companion. -/
def nonlinearPairing (n k : ℕ) (x y : Fin (2*n) → ℂ) : ℂ :=
  inner ℂ (radialIncidentSynthesis k (2*n) (jetValues n k x))
    (radialCompletedRemainderSynthesis k (2*n) (jetValues n k y))+
  inner ℂ (radialCompletedRemainderSynthesis k (2*n) (jetValues n k x))
    (radialIncidentSynthesis k (2*n) (jetValues n k y))

theorem nonlinearPairing_self_re (n k : ℕ) (x : Fin (2*n) → ℂ) :
    (nonlinearPairing n k x x).re = nonlinearReadout n k x/2 := by
  have hc := congrArg Complex.re (inner_conj_symm
    (radialIncidentSynthesis k (2*n) (jetValues n k x))
    (radialCompletedRemainderSynthesis k (2*n) (jetValues n k x)))
  simp only [Complex.conj_re] at hc
  unfold nonlinearPairing nonlinearReadout
  rw [Complex.add_re]
  linarith

/-- The complete signed budget is a mixed slope pairing, not an imposed norm. -/
theorem budget_slope_polarized (n k : ℕ) (x y : Fin (2*n) → ℂ)
    (hs : strip k (2*n))
    (hF : ∀ r : Fin (2*n), completedNativeOperatorCharacteristic (radialPoint k r) ≠ 0)
    (hP : ∀ r : Fin (2*n), completedNativePositiveHermiteBiehlerCoordinate (radialPoint k r) ≠ 0) :
    jetBudget n k x y hs =
      inner ℂ (radialIncidentSynthesis k (2*n) (jetValues n k x))
        (radialIncidentSynthesis k (2*n) (fun r => jetValues n k y r*radialCompletedSlope k r))+
      inner ℂ (radialIncidentSynthesis k (2*n) (fun r => jetValues n k x r*radialCompletedSlope k r))
        (radialIncidentSynthesis k (2*n) (jetValues n k y)) := by
  rw [jetBudget_eq_original_pairing n k x y hs hP, jet_pairing_source_balance n k x y hP]
  unfold polarizedSourceBalance
  rw [chiral_pairing_balance, sourceValue_eq_completedCoefficients,
    sourceValue_eq_completedCoefficients, sourceCompanion_eq_completedSlope k (2*n) _ hF,
    sourceCompanion_eq_completedSlope k (2*n) _ hF, inner_smul_left, inner_smul_right,
    Complex.conj_I]
  ring_nf
  simp [jetValues, Complex.I_sq]

/-- Exact extraction for two independent enriched inputs. No crossing,
quadrature, completion or nonlinear companion is removed. -/
theorem budget_euler_polarized (n k : ℕ) (x y : Fin (2*(n+1)) → ℂ)
    (hs : strip k (2*(n+1)))
    (hF : ∀ r : Fin (2*(n+1)), completedNativeOperatorCharacteristic (radialPoint k r) ≠ 0)
    (hP : ∀ r : Fin (2*(n+1)), completedNativePositiveHermiteBiehlerCoordinate (radialPoint k r) ≠ 0) :
    jetBudget (n+1) k x y hs =
      (canonicalCompletedNativeLogDerivativeMoment 0:ℂ)*conj (x 0)*y 0+
        nonlinearPairing (n+1) k x y := by
  rw [budget_slope_polarized (n+1) k x y hs hF hP,
    radialCompletedSlopeSynthesis_eq_euler_add_remainder,
    radialCompletedSlopeSynthesis_eq_euler_add_remainder]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal]
  have hb := radialEuler_boundary_polarized k (2*(n+1))
    (jetValues (n+1) k x) (jetValues (n+1) k y)
  rw [jet_values_sum n k x hF hP, jet_values_sum n k y hF hP] at hb
  have he : (radialCompletedEulerScale k:ℂ)*
      (inner ℂ (radialIncidentSynthesis k (2*(n+1)) (jetValues (n+1) k x))
        (radialEulerSynthesis k (2*(n+1)) (jetValues (n+1) k y))+
       inner ℂ (radialEulerSynthesis k (2*(n+1)) (jetValues (n+1) k x))
        (radialIncidentSynthesis k (2*(n+1)) (jetValues (n+1) k y))) =
      (canonicalCompletedNativeLogDerivativeMoment 0:ℂ)*conj (x 0)*y 0 := by
    rw [hb, euler_scale_native]
    have hs2 : (Real.sqrt 2:ℂ)^2=2 := by
      norm_cast
      exact Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    have hk : ((k:ℝ)+1:ℂ) ≠ 0 := by exact_mod_cast (show (k:ℝ)+1 ≠ 0 by positivity)
    simp only [map_mul, map_inv₀, Complex.conj_ofReal, Complex.ofReal_div,
      Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_add, Complex.ofReal_one]
    field_simp [hk]
    linear_combination -hs2*(canonicalCompletedNativeLogDerivativeMoment 0:ℂ)*conj (x 0)*y 0
  unfold nonlinearPairing
  linear_combination he

end
end CarryResidualEuler
