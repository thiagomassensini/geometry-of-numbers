import AllOrderTail
import PhysicalMaterialVariation

namespace CarryJetVariationBudget
open CarryMaterialVariation CarryAllOrderTail
open scoped BigOperators ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

def size (N : ℕ) (x : Fin N → ℂ) : ℝ := ∑ i, ‖x i‖

/-- Comparison of the full polarized moving-input variations. Both source
arguments and their velocities remain independent. -/
theorem variation_error_bound (N : ℕ) (t : ℝ)
    (r dr s ds x dx y dy : Fin N → ℂ) (ε η : ℝ)
    (hε : 0 ≤ ε) (hη : 0 ≤ η)
    (hr : ∀ i, ‖r i-s i‖ ≤ ε) (hd : ∀ i, ‖dr i-ds i‖ ≤ η) :
    ‖materialVariation N t r dr x dx y dy-materialVariation N t s ds x dx y dy‖ ≤
      ‖(2/(t:ℂ))‖ * (ε*size N dx*size N y + ε*size N x*size N dy) +
      ‖(2/(t:ℂ)^2)‖ * ((|t| *η+ε)*size N x*size N y) := by
  have h1 := material_pair_uniform_error N r s dx y ε hε hr
  have h2 := material_pair_uniform_error N r s x dy ε hε hr
  have hδ : 0 ≤ |t| *η+ε := by positivity
  have hi (i : Fin N) : ‖((t:ℂ)*dr i-r i)-((t:ℂ)*ds i-s i)‖ ≤ |t| *η+ε := by
    have he : ((t:ℂ)*dr i-r i)-((t:ℂ)*ds i-s i) =
      (t:ℂ)*(dr i-ds i)-(r i-s i) := by ring
    rw [he]
    calc
      _ ≤ ‖(t:ℂ)*(dr i-ds i)‖+‖r i-s i‖ := norm_sub_le _ _
      _ = |t| *‖dr i-ds i‖+‖r i-s i‖ := by rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (hd i) (abs_nonneg t)) (hr i)
  have h3 := material_pair_uniform_error N (fun i => (t:ℂ)*dr i-r i)
      (fun i => (t:ℂ)*ds i-s i) x y (|t| *η+ε) hδ hi
  have he : materialVariation N t r dr x dx y dy-materialVariation N t s ds x dx y dy =
      (2/(t:ℂ))*(materialPair N r dx y-materialPair N s dx y) +
      (2/(t:ℂ))*(materialPair N r x dy-materialPair N s x dy) +
      (2/(t:ℂ)^2)*(materialPair N (fun i => (t:ℂ)*dr i-r i) x y-
        materialPair N (fun i => (t:ℂ)*ds i-s i) x y) := by
    unfold materialVariation
    ring
  rw [he]
  calc
    _ ≤ ‖(2/(t:ℂ))*(materialPair N r dx y-materialPair N s dx y)‖+
        ‖(2/(t:ℂ))*(materialPair N r x dy-materialPair N s x dy)‖+
        ‖(2/(t:ℂ)^2)*(materialPair N (fun i => (t:ℂ)*dr i-r i) x y-
          materialPair N (fun i => (t:ℂ)*ds i-s i) x y)‖ := by
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
    _ ≤ _ := by
      simp only [norm_mul]
      unfold size
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left h1 (norm_nonneg _))
        (mul_le_mul_of_nonneg_left h2 (norm_nonneg _)))
        (mul_le_mul_of_nonneg_left h3 (norm_nonneg _)) |>.trans_eq (by ring)


/-- The variation bound applies to the derivative of the original completed
physical source once the already established physical-domain hypotheses hold. -/
theorem physical_derivative_approximation (N : ℕ) (x y : ℝ → Fin N → ℂ) (t : ℝ)
    (s ds : Fin N → ℂ) (ε η : ℝ) (ht : 0 < t)
    (hx : ∀ i, DifferentiableAt ℝ (fun h => x h i) t)
    (hy : ∀ i, DifferentiableAt ℝ (fun h => y h i) t)
    (hD : ∀ i : Fin N, CarryMovingRadial.point t i ∈ CarrySelfAdjointOperator.completedNativeHeightDomain)
    (hF : ∀ i : Fin N, CarrySelfAdjointOperator.completedNativeOperatorCharacteristic (CarryMovingRadial.point t i) ≠ 0)
    (hP : ∀ i : Fin N, CarrySelfAdjointOperator.completedNativePositiveHermiteBiehlerCoordinate (CarryMovingRadial.point t i) ≠ 0)
    (hε : 0 ≤ ε) (hη : 0 ≤ η)
    (hr : ∀ i : Fin N, ‖CarryMovingRadial.rho t i-s i‖ ≤ ε)
    (hd : ∀ i, ‖rhoVelocity N t i-ds i‖ ≤ η) :
    ‖deriv (fun h => 2*CarrySelfAdjointOperator.canonicalCompletedNativeProjectiveChiralForm
        (CarryMovingRadial.curveState N h (x h)) (CarryMovingRadial.curveState N h (y h))) t -
      materialVariation N t s ds (x t) (rawVelocity N x t) (y t) (rawVelocity N y t)‖ ≤
      ‖(2/(t:ℂ))‖ * (ε*size N (rawVelocity N x t)*size N (y t) +
        ε*size N (x t)*size N (rawVelocity N y t)) +
      ‖(2/(t:ℂ)^2)‖ * ((|t| *η+ε)*size N (x t)*size N (y t)) := by
  rw [physical_material_derivative N x y t ht hx hy hD hF hP]
  exact variation_error_bound N t _ _ s ds _ _ _ _ ε η hε hη hr hd

end
end CarryJetVariationBudget
