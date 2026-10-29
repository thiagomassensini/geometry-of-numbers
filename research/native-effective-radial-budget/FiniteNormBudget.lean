import SixEffectiveRemainder

namespace CarryEffectiveRadial
open CarrySelfAdjointOperator CarryMaterialVariation
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000

theorem finite_norm_budget {ι : Type*} [Fintype ι] (c m : ι → ℂ)
    (hm : ∀ i, ‖m i‖ ≤ 1) : ‖∑ i, c i*m i‖ ≤ ∑ i, ‖c i‖ := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (hm i)

def nodeMonomials (u v : ℝ) (z : ℂ) : Fin 6 → ℂ :=
  ![(u:ℂ)^2*z^4,(u:ℂ)*(v:ℂ)*z^6,(u:ℂ)*z^2,(v:ℂ)^2*z^8,(v:ℂ)*z^4,1]
def nodeCoefficients : Fin 6 → Fin 6 → ℂ :=
  ![![40,-1040,-62/21,4800,320/7,1/21],
    ![-40,1280,85/21,-2400,-710/7,-5/84],
    ![120/7,-720,-65/21,0,120,5/126],
    ![-20/7,160,92/63,0,-80,-1/63],
    ![0,0,-25/63,0,200/7,5/1386],
    ![0,0,1/21,0,-30/7,-1/2772]]

theorem node_coefficients_exact (u v : ℝ) (z : ℂ) (j : Fin 6) :
    sixNodeWeight u v z j=∑ i : Fin 6, nodeCoefficients j i*nodeMonomials u v z i := by
  fin_cases j <;> norm_num [sixNodeWeight,nodeCoefficients,nodeMonomials,Fin.sum_univ_succ] <;> ring

theorem six_node_weight_bound (u v : ℝ) (z : ℂ) (hu : |u|≤1) (hv : |v|≤1)
    (hz : ‖z‖≤1) (j : Fin 6) : ‖sixNodeWeight u v z j‖≤100000 := by
  have huN : ‖(u:ℂ)‖≤1 := by simpa using hu
  have hvN : ‖(v:ℂ)‖≤1 := by simpa using hv
  have hm (i : Fin 6) : ‖nodeMonomials u v z i‖≤1 := by
    fin_cases i <;> dsimp [nodeMonomials] <;> simp only [norm_mul,norm_pow,norm_one] <;> bound
  rw [node_coefficients_exact]
  apply (finite_norm_budget _ _ hm).trans
  fin_cases j <;> norm_num [nodeCoefficients,Fin.sum_univ_succ,norm_div]

def higherMonomials (u v : ℝ) (z : ℂ) : Fin 12 → ℂ :=
  ![(canonicalCompletedNativeLogDerivativeMoment 3:ℂ)*(v:ℂ)^2,
    (canonicalCompletedNativeLogDerivativeMoment 4:ℂ)*(u:ℂ)*(v:ℂ),
    (canonicalCompletedNativeLogDerivativeMoment 5:ℂ)*(u:ℂ)^2,
    (canonicalCompletedNativeLogDerivativeMoment 5:ℂ)*(v:ℂ),
    (canonicalCompletedNativeLogDerivativeMoment 6:ℂ)*(u:ℂ),
    (canonicalCompletedNativeLogDerivativeMoment 4:ℂ)*(v:ℂ)^2*z^2,
    (canonicalCompletedNativeLogDerivativeMoment 5:ℂ)*(u:ℂ)*(v:ℂ)*z^2,
    (canonicalCompletedNativeLogDerivativeMoment 6:ℂ)*(u:ℂ)^2*z^2,
    (canonicalCompletedNativeLogDerivativeMoment 6:ℂ)*(v:ℂ)*z^2,
    (canonicalCompletedNativeLogDerivativeMoment 5:ℂ)*(v:ℂ)^2*z^4,
    (canonicalCompletedNativeLogDerivativeMoment 6:ℂ)*(u:ℂ)*(v:ℂ)*z^4,
    (canonicalCompletedNativeLogDerivativeMoment 6:ℂ)*(v:ℂ)^2*z^6]
def higherCoefficients : Fin 12 → ℂ :=
  ![42,3948,1254,65868,32032,-170,-75856,-22880,-3649360,682,1333332,-2730]

theorem six_higher_polynomial_bound (u v : ℝ) (z : ℂ) (hu : |u|≤1) (hv : |v|≤1)
    (hz : ‖z‖≤1) : ‖sixHigherPolynomial u v z‖≤10000000000 := by
  have huN : ‖(u:ℂ)‖≤1 := by simpa using hu
  have hvN : ‖(v:ℂ)‖≤1 := by simpa using hv
  have hm (i : Fin 12) : ‖higherMonomials u v z i‖≤1 := by
    have h3 := canonical_moment_norm_le_one 3
    have h4 := canonical_moment_norm_le_one 4
    have h5 := canonical_moment_norm_le_one 5
    have h6 := canonical_moment_norm_le_one 6
    fin_cases i <;> dsimp [higherMonomials] <;> simp only [norm_mul,norm_pow] <;> bound
  have he : sixHigherPolynomial u v z=∑ i : Fin 12, higherCoefficients i*higherMonomials u v z i := by
    norm_num [sixHigherPolynomial,higherCoefficients,higherMonomials,Fin.sum_univ_succ]
    ring
  rw [he]
  apply (finite_norm_budget _ _ hm).trans
  norm_num [higherCoefficients,Fin.sum_univ_succ]

theorem six_effective_remainder_bound (u v : ℝ) (z : ℂ) (hu : |u|≤1) (hv : |v|≤1)
    (hz : ‖z‖≤1/12) : ‖sixEffectiveRemainder u v z‖ ≤ (10:ℝ)^20 := by
  have hz1 : ‖z‖≤1 := by linarith
  have hG (j : Fin 6) : ‖sourceRemainder 7 (Complex.I*((j:ℂ)+1)*z)‖≤1 :=
    source_remainder_norm_le_one 7 _ (lt_of_le_of_lt (radial_node_norm z j) (by linarith))
  have hj (j : Fin 6) : ‖(j:ℂ)+1‖ ≤ 6 := by
    have he : ((j:ℂ)+1)=((((j:ℝ)+1):ℝ):ℂ) := by push_cast; rfl
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact_mod_cast (show (j:ℕ)+1≤6 by omega)
  have ht (j : Fin 6) : ‖sixNodeWeight u v z j*((j:ℂ)+1)^15*
      sourceRemainder 7 (Complex.I*((j:ℂ)+1)*z)‖≤100000*(6:ℝ)^15 := by
    rw [norm_mul,norm_mul,norm_pow]
    exact mul_le_of_le_one_right (by positivity) (hG j) |>.trans
      (mul_le_mul (six_node_weight_bound u v z hu hv hz1 j)
        (pow_le_pow_left₀ (norm_nonneg _) (hj j) _) (by positivity) (by norm_num))
  have hs : ‖∑ j : Fin 6, sixNodeWeight u v z j*((j:ℂ)+1)^15*
      sourceRemainder 7 (Complex.I*((j:ℂ)+1)*z)‖≤6*(100000*(6:ℝ)^15) := by
    apply (norm_sum_le _ _).trans
    have hh := Finset.sum_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin 6))) => ht j)
    simpa using hh
  unfold sixEffectiveRemainder
  have hn := norm_sub_le (sixHigherPolynomial u v z)
    ((∑ j : Fin 6, sixNodeWeight u v z j*((j:ℂ)+1)^15*
      sourceRemainder 7 (Complex.I*((j:ℂ)+1)*z))/14400)
  rw [norm_div] at hn
  norm_num only [Complex.norm_ofNat] at hn
  have hp := six_higher_polynomial_bound u v z hu hv hz1
  norm_num at hs
  linarith

theorem six_effective_remainder_deriv_bound (u v : ℝ) (z : ℂ) (hu : |u|≤1) (hv : |v|≤1)
    (hz : ‖z‖≤1/1000) : ‖deriv (sixEffectiveRemainder u v) z‖≤(10:ℝ)^22 := by
  have ha : AnalyticOnNhd ℂ (sixEffectiveRemainder u v) (Metric.closedBall z (1/100)) := by
    intro w hw
    apply six_effective_remainder_analytic u v w
    have hd := Metric.mem_closedBall.mp hw
    rw [dist_eq_norm] at hd
    have ht := norm_add_le (w-z) z
    rw [sub_add_cancel] at ht
    linarith
  have hd : DiffContOnCl ℂ (sixEffectiveRemainder u v) (Metric.ball z (1/100)) :=
    (ha.differentiableOn.mono Metric.closure_ball_subset_closedBall).diffContOnCl
  have hb : ∀ w ∈ Metric.sphere z (1/100), ‖sixEffectiveRemainder u v w‖≤(10:ℝ)^20 := by
    intro w hw
    apply six_effective_remainder_bound u v w hu hv
    have he := Metric.mem_sphere.mp hw
    rw [dist_eq_norm] at he
    have ht := norm_add_le (w-z) z
    rw [sub_add_cancel] at ht
    linarith
  have hh := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0:ℝ)<1/100) hd hb
  norm_num at hh ⊢
  exact hh

end
end CarryEffectiveRadial
