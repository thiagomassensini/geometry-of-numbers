import CauchyFrame

namespace CarryCauchyResidual
open CarrySelfAdjointOperator ChiralReturn CarryReturnDeflation CarryPositiveSquare
open scoped InnerProductSpace ComplexConjugate BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000

/-- The unchanged completed return at the unchanged radial address. -/
def sourceReturn (k n : ℕ) : ℂ := completedNativeHermiteBiehlerChiralQuotient
  (canonicalCompletedC3RadialTiltPoint k n)

def feedbackDenominator (k n : ℕ) : ℂ := 1-conj (oneReturn k)*sourceReturn k n
def incidentCoefficient (k n : ℕ) : ℂ :=
  ((n:ℂ)/((n:ℂ)+2))*feedbackDenominator k n
def returnedCoefficient (k n : ℕ) : ℂ := sourceReturn k n-oneReturn k

theorem nativeIn_basis (k N : ℕ) (i : Fin N) :
    nativeIn k N (Pi.single i 1) = feedbackDenominator k i • feature k i := by
  simp only [nativeIn, LinearMap.sub_apply, LinearMap.smul_apply,
    radialIncidentSynthesis, radialReturnedSynthesis, LinearMap.coe_mk, AddHom.coe_mk,
    completedNativeRadialChiralMultiplierState]
  simp only [Pi.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  simp only [feedbackDenominator, sourceReturn, feature, smul_smul, sub_smul, one_smul]

theorem nativeOut_basis (k N : ℕ) (i : Fin N) :
    nativeOut k N (Pi.single i 1) = returnedCoefficient k i • feature k i := by
  simp only [nativeOut, LinearMap.sub_apply, LinearMap.smul_apply,
    radialIncidentSynthesis, radialReturnedSynthesis, LinearMap.coe_mk, AddHom.coe_mk,
    completedNativeRadialChiralMultiplierState]
  simp only [Pi.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rw [returnedCoefficient, sub_smul]
  rfl

theorem remainingIncident_basis (k N : ℕ) (i : Fin N) :
    remainingIncident k N (Pi.single i 1) =
      feedbackDenominator k i • perpendicularFeature k i := by
  change nativeIn k N _ - nativeBoundaryProjection k (nativeIn k N _) = _
  rw [nativeIn_basis, map_smul, ← smul_sub, ← perpendicularFeature_eq_complement]

theorem remainingIncident_basis_isometric (k N : ℕ) (i : Fin N) (hi : i.val ≠ 0) :
    remainingIncident k N (Pi.single i 1) = incidentCoefficient k i • isometricFeature k i := by
  rw [remainingIncident_basis]
  have hi' : (i.val:ℂ) ≠ 0 := by exact_mod_cast hi
  have hp : (i.val:ℂ)+2 ≠ 0 := by exact_mod_cast (show (i.val:ℝ)+2 ≠ 0 by positivity)
  simp only [incidentCoefficient, isometricFeature, smul_smul]
  congr 1
  field_simp

theorem residual_basis_kernel (k N : ℕ) (i j : Fin N) :
    remainingPair k N (Pi.single i 1) (Pi.single j 1) =
      cauchy k i j * (conj (incidentCoefficient k i)*incidentCoefficient k j-
        conj (returnedCoefficient k i)*returnedCoefficient k j) := by
  rw [remainingPair, remainingIncident_basis, remainingIncident_basis,
    nativeOut_basis, nativeOut_basis]
  simp only [inner_smul_left, inner_smul_right, perpendicularFeature_inner,
    feature_inner, incidentCoefficient, map_mul, map_div₀, map_add, map_natCast, map_ofNat]
  ring

/-- Inclusion of all remaining coefficients; the eliminated head is zero. -/
def tailInput {N : ℕ} (c : Fin N → ℂ) : Fin (N+1) → ℂ := Fin.cons 0 c

def tailCoefficients {N : ℕ} (c : Fin (N+1) → ℂ) : Fin N → ℂ := fun i => c i.succ

theorem eraseHead_eq_tail (N : ℕ) (c : Fin (N+1) → ℂ) :
    eraseHead c = tailInput (tailCoefficients c) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [eraseHead, tailInput]
  · simp [eraseHead, tailInput, tailCoefficients]

theorem linearMap_tail (N : ℕ) (L : (Fin (N+1) → ℂ) →ₗ[ℂ] Physical)
    (c : Fin N → ℂ) :
    L (tailInput c) = ∑ i : Fin N, c i • L (Pi.single i.succ 1) := by
  classical
  have h : tailInput c = ∑ i : Fin (N+1), (tailInput c i) • Pi.single i 1 := by
    funext j
    simp [Pi.single_apply]
  rw [h, map_sum]
  simp only [map_smul, Fin.sum_univ_succ, tailInput, Fin.cons_zero, Fin.cons_succ,
    zero_smul, zero_add]

def incidentCoordinates (k N : ℕ) (c : Fin N → ℂ) : Fin N → ℂ :=
  fun i => c i*incidentCoefficient k (i.val+1)
def returnedCoordinates (k N : ℕ) (c : Fin N → ℂ) : Fin N → ℂ :=
  fun i => c i*returnedCoefficient k (i.val+1)

theorem incidentCoordinates_injective (k N : ℕ)
    (ha : ∀ i : Fin N, incidentCoefficient k (i.val+1) ≠ 0) :
    Function.Injective (incidentCoordinates k N) := by
  intro c d h
  funext i
  exact mul_right_cancel₀ (ha i) (congrFun h i)

/-- Vector identity in the original carrier, before any norm is taken. -/
theorem remainingIncident_tail (k N : ℕ) (c : Fin N → ℂ) :
    remainingIncident k (N+1) (tailInput c) =
      isometricSynthesis k N (incidentCoordinates k N c) := by
  rw [linearMap_tail]
  have he (i : Fin N) := remainingIncident_basis_isometric k (N+1) i.succ (by simp)
  simp only [he,
    isometricSynthesis, LinearMap.coe_mk, AddHom.coe_mk, incidentCoordinates,
    Fin.val_succ, smul_smul]

/-- The returned channel is not projected or discarded. -/
theorem nativeOut_tail (k N : ℕ) (c : Fin N → ℂ) :
    nativeOut k (N+1) (tailInput c) = tailSynthesis k N (returnedCoordinates k N c) := by
  rw [linearMap_tail]
  simp only [nativeOut_basis, tailSynthesis, LinearMap.coe_mk, AddHom.coe_mk,
    returnedCoordinates, Fin.val_succ, smul_smul]

/-- Exact closure on the SAME Cauchy Gram, including every cross term.
No contractivity, moment sign, or higher Schur hypothesis occurs. -/
theorem residual_same_cauchy (k N : ℕ) (c d : Fin N → ℂ) :
    remainingPair k (N+1) (tailInput c) (tailInput d) =
      inner ℂ (tailSynthesis k N (incidentCoordinates k N c))
        (tailSynthesis k N (incidentCoordinates k N d)) -
      inner ℂ (tailSynthesis k N (returnedCoordinates k N c))
        (tailSynthesis k N (returnedCoordinates k N d)) := by
  rw [remainingPair, remainingIncident_tail, remainingIncident_tail,
    nativeOut_tail, nativeOut_tail, synthesis_isometry]

/-- The head is eliminated algebraically in both slots, so this identity
applies to complete native jet inputs, not only to hand-picked tail inputs. -/
theorem residual_full_source (k N : ℕ) (c d : Fin (N+1) → ℂ) :
    remainingPair k (N+1) c d =
      inner ℂ (tailSynthesis k N (incidentCoordinates k N (tailCoefficients c)))
        (tailSynthesis k N (incidentCoordinates k N (tailCoefficients d))) -
      inner ℂ (tailSynthesis k N (returnedCoordinates k N (tailCoefficients c)))
        (tailSynthesis k N (returnedCoordinates k N (tailCoefficients d))) := by
  rw [remainingPair_eraseHead, eraseHead_eq_tail, eraseHead_eq_tail, residual_same_cauchy]

/-- Forced fractional return in these isometric coordinates; denominators
are kept explicit and their nonvanishing is proved from the source later. -/
def reducedReturn (k n : ℕ) : ℂ := returnedCoefficient k n/incidentCoefficient k n

theorem reducedReturn_formula (k n : ℕ) :
    reducedReturn k n = (((n:ℂ)+2)/(n:ℂ))*
      ((sourceReturn k n-oneReturn k)/(1-conj (oneReturn k)*sourceReturn k n)) := by
  simp only [reducedReturn, returnedCoefficient, incidentCoefficient, feedbackDenominator,
    div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

theorem reduced_coordinates_exact (k N : ℕ) (c : Fin N → ℂ)
    (ha : ∀ i : Fin N, incidentCoefficient k (i.val+1) ≠ 0) :
    returnedCoordinates k N c =
      fun i => incidentCoordinates k N c i * reducedReturn k (i.val+1) := by
  funext i
  simp only [returnedCoordinates, incidentCoordinates, reducedReturn]
  field_simp [ha i]

/-- Existence of these coordinates does not supply the sign: the remaining
norm comparison concerns the actual completed quotient in reducedReturn. -/
theorem residual_return_comparison (k N : ℕ) (c : Fin N → ℂ)
    (ha : ∀ i : Fin N, incidentCoefficient k (i.val+1) ≠ 0) :
    (remainingPair k (N+1) (tailInput c) (tailInput c)).re =
      ‖tailSynthesis k N (incidentCoordinates k N c)‖^2-
      ‖tailSynthesis k N (fun i => incidentCoordinates k N c i * reducedReturn k (i.val+1))‖^2 := by
  rw [residual_same_cauchy, reduced_coordinates_exact k N c ha]
  simp only [Complex.sub_re, physical_inner_self_re]

end
end CarryCauchyResidual
