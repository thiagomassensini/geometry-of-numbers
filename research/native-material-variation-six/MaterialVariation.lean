import CompletionCancellation
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.RealDeriv

namespace CarryMaterialVariation
open CarryMovingRadial
open scoped BigOperators ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000

def materialPair (N : ℕ) (r x y : Fin N → ℂ) : ℂ :=
  ∑ i : Fin N, ∑ j : Fin N, conj (x i)*y j*(r i+r j)/((i:ℂ)+(j:ℂ)+2)

def materialVariation (N : ℕ) (t : ℝ) (r dr x dx y dy : Fin N → ℂ) : ℂ :=
  (2/(t:ℂ))*(materialPair N r dx y+materialPair N r x dy)+
    (2/(t:ℂ)^2)*materialPair N (fun i => (t:ℂ)*dr i-r i) x y

theorem materialPair_affine (N : ℕ) (r s x y : Fin N → ℂ) (t : ℂ) :
    materialPair N (fun i => t*s i-r i) x y=
      t*materialPair N s x y-materialPair N r x y := by
  unfold materialPair
  rw [Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Independent material inputs and all crossed variations; no sign or Gram
assumption is used to differentiate the completed source readout. -/
theorem materialPair_hasDerivAt (N : ℕ) (r x y : ℝ → Fin N → ℂ)
    (dr dx dy : Fin N → ℂ) (t : ℝ)
    (hr : ∀ i, HasDerivAt (fun h => r h i) (dr i) t)
    (hx : ∀ i, HasDerivAt (fun h => x h i) (dx i) t)
    (hy : ∀ i, HasDerivAt (fun h => y h i) (dy i) t) :
    HasDerivAt (fun h => materialPair N (r h) (x h) (y h))
      (materialPair N (r t) dx (y t)+materialPair N (r t) (x t) dy+
        materialPair N dr (x t) (y t)) t := by
  have hh := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
      ((((hx i).star.mul (hy j)).mul ((hr i).add (hr j))).div_const ((i:ℂ)+(j:ℂ)+2))))
  convert hh using 1
  all_goals try rfl
  unfold materialPair
  simp only [Pi.mul_apply,Pi.add_apply,starRingEnd_apply]
  simp_rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Closed material formula: x' terms plus h*rho' - rho, with the original
2/h and 2/h^2 factors. Completion has already been synthesized exactly. -/
theorem scaled_material_hasDerivAt (N : ℕ) (r x y : ℝ → Fin N → ℂ)
    (dr dx dy : Fin N → ℂ) (t : ℝ) (ht : t≠0)
    (hr : ∀ i, HasDerivAt (fun h => r h i) (dr i) t)
    (hx : ∀ i, HasDerivAt (fun h => x h i) (dx i) t)
    (hy : ∀ i, HasDerivAt (fun h => y h i) (dy i) t) :
    HasDerivAt (fun h : ℝ => (2/(h:ℂ))*materialPair N (r h) (x h) (y h))
      (materialVariation N t (r t) dr (x t) dx (y t) dy) t := by
  have hn : (t:ℂ)≠0 := by exact_mod_cast ht
  have hs : HasDerivAt (fun h : ℝ => (2/(h:ℂ))) (-2/(t:ℂ)^2) t := by
    simpa using (((hasDerivAt_const (t:ℂ) (2:ℂ)).div (hasDerivAt_id (t:ℂ)) hn).comp_ofReal)
  have hh := hs.mul (materialPair_hasDerivAt N r x y dr dx dy t hr hx hy)
  convert hh using 1
  all_goals try rfl
  unfold materialVariation
  rw [materialPair_affine]
  field_simp [hn]
  ring

end
end CarryMaterialVariation
