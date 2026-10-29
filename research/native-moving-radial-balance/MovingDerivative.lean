import CurvePairing
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.RealDeriv

namespace CarryMovingRadial
open scoped BigOperators ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000

def returnVariation (N : ℕ) (q dq c d : Fin N → ℂ) : ℂ :=
  -∑ i : Fin N, ∑ j : Fin N,
    conj (c i)*d j*(conj (dq i)*q j+conj (q i)*dq j)/((i:ℂ)+(j:ℂ)+2)

/-- Both coefficient paths are independent; all four kinds of variation
are retained before taking a real part or a diagonal. -/
theorem fullPair_hasDerivAt (N : ℕ) (q c d : ℝ → Fin N → ℂ)
    (dq dc dd : Fin N → ℂ) (t : ℝ)
    (hq : ∀ i, HasDerivAt (fun h => q h i) (dq i) t)
    (hc : ∀ i, HasDerivAt (fun h => c h i) (dc i) t)
    (hd : ∀ i, HasDerivAt (fun h => d h i) (dd i) t) :
    HasDerivAt (fun h => fullPair N (q h) (c h) (d h))
      (fullPair N (q t) dc (d t)+fullPair N (q t) (c t) dd+
        returnVariation N (q t) dq (c t) (d t)) t := by
  have hh := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
      ((((hc i).star.mul (hd j)).mul
        ((hasDerivAt_const t (1:ℂ)).sub ((hq i).star.mul (hq j)))).div_const
          ((i:ℂ)+(j:ℂ)+2))))
  convert hh using 1
  all_goals try rfl
  unfold fullPair returnVariation
  simp only [Pi.sub_apply,Pi.mul_apply,starRingEnd_apply]
  simp_rw [← Finset.sum_neg_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem fullPair_derivative (N : ℕ) (q c : ℝ → Fin N → ℂ) (t : ℝ)
    (hq : ∀ i, DifferentiableAt ℝ (fun h => q h i) t)
    (hc : ∀ i, DifferentiableAt ℝ (fun h => c h i) t) :
    deriv (fun h => fullPair N (q h) (c h) (c h)) t=
      fullPair N (q t) (fun i => deriv (fun h => c h i) t) (c t)+
      fullPair N (q t) (c t) (fun i => deriv (fun h => c h i) t)+
      returnVariation N (q t) (fun i => deriv (fun h => q h i) t) (c t) (c t) := by
  exact (fullPair_hasDerivAt N q c c _ _ _ t
    (fun i => (hq i).hasDerivAt) (fun i => (hc i).hasDerivAt)
    (fun i => (hc i).hasDerivAt)).deriv

end
end CarryMovingRadial
