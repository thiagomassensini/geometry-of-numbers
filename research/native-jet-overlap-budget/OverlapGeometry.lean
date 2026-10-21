import NativeCauchyOverlap
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-! Exact geometry of the ORIGINAL Cauchy overlap. No source is replaced. -/
namespace CarryJetOverlap
open CarrySelfAdjointOperator CarryFiberTransport ChiralReturn
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section

abbrev observedCauchy (k i : ℕ) :=
  (Real.sqrt (2*(radialPoint k i).im) : ℂ) • radialField k i

/-- The old diagonal observation cancels the radial scale exactly. -/
theorem observedCauchy_eq (k i : ℕ) :
    observedCauchy k i =
      (Real.sqrt (2*((i : ℝ)+1)) : ℂ) • completedNativeChiralCauchyFeature i := by
  have hk : (k : ℝ)+1 ≠ 0 := by positivity
  have hscalar : Real.sqrt (2*((i : ℝ)+1)*((k : ℝ)+1)⁻¹)*
      Real.sqrt ((k : ℝ)+1)=Real.sqrt (2*((i : ℝ)+1)) := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ 2*((i : ℝ)+1)*((k : ℝ)+1)⁻¹)]
    congr 1
    field_simp
  unfold observedCauchy radialField completedNativeRadialChiralCauchyState
  rw [smul_smul,← Complex.ofReal_mul]
  congr 1
  exact_mod_cast (by simpa only [canonicalCompletedC3RadialTiltPoint_im,mul_assoc] using hscalar :
    Real.sqrt (2*(radialPoint k i).im)*Real.sqrt ((k : ℝ)+1)=Real.sqrt (2*((i : ℝ)+1)))

/-- The overlap is not an error tending to zero with the mesh. -/
theorem radialOverlap_independent (k l i j : ℕ) :
    radialOverlap k i j=radialOverlap l i j := by
  rw [radialOverlap_inner,radialOverlap_inner]
  change inner ℂ (observedCauchy k i) (observedCauchy k j)=
    inner ℂ (observedCauchy l i) (observedCauchy l j)
  simp only [observedCauchy_eq]

theorem radialOverlap_closed (k i j : ℕ) :
    radialOverlap k i j=
      (((Real.sqrt (2*((i : ℝ)+1))*Real.sqrt (2*((j : ℝ)+1)) /
        ((i : ℝ)+(j : ℝ)+2)) : ℝ) : ℂ) := by
  rw [radialOverlap_inner]
  change inner ℂ (observedCauchy k i) (observedCauchy k j)=_
  rw [observedCauchy_eq,observedCauchy_eq,inner_smul_left,inner_smul_right,
    inner_completedNativeChiralCauchyFeature]
  simp only [Complex.conj_ofReal,div_eq_mul_inv]
  push_cast
  ring

/-- Finite synthesis of the SAME observed Cauchy vectors, before pairing. -/
def observedSynthesis (k : ℕ) {N : ℕ} (c : Fin N → ℂ) :
    CanonicalCompletedNativeChiralCauchyCarrier := ∑ i, c i • observedCauchy k i

theorem observedSynthesis_pairing (k : ℕ) {N : ℕ} (c d : Fin N → ℂ) :
    inner ℂ (observedSynthesis k c) (observedSynthesis k d)=
      ∑ i, ∑ j, conj (c i)*d j*radialOverlap k i j := by
  unfold observedSynthesis
  rw [sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [inner_smul_left,inner_smul_right]
  change conj (c i)*(d j*inner ℂ (observedCauchy k i) (observedCauchy k j))=_
  rw [← radialOverlap_inner]
  ring

/-- The ones-minus-overlap kernel has a signed energy interpretation,
with two independent coefficient families and all ordered crosses. -/
theorem complement_pairing (k : ℕ) {N : ℕ} (c d : Fin N → ℂ) :
    (∑ i, ∑ j, conj (c i)*d j*(1-radialOverlap k i j))=
      conj (∑ i, c i)*(∑ j, d j)-
        inner ℂ (observedSynthesis k c) (observedSynthesis k d) := by
  rw [observedSynthesis_pairing]
  simp_rw [mul_sub,mul_one]
  simp_rw [Finset.sum_sub_distrib]
  simp only [map_sum,Finset.sum_mul,Finset.mul_sum]
  congr 1
  exact Finset.sum_comm

/-- On zero-sum coefficients the overlap correction has the opposite sign
from a positive Gram. This is not yet the source-weighted Gamma budget. -/
theorem complement_zero_sum (k : ℕ) {N : ℕ} (c : Fin N → ℂ)
    (hc : ∑ i, c i=0) :
    (∑ i, ∑ j, conj (c i)*c j*(1-radialOverlap k i j)).re=
      -‖observedSynthesis k c‖^2 := by
  rw [complement_pairing,hc,map_zero,zero_mul,zero_sub]
  simp [inner_self_eq_norm_sq_to_K,← Complex.ofReal_pow]

theorem complement_zero_sum_nonpos (k : ℕ) {N : ℕ} (c : Fin N → ℂ)
    (hc : ∑ i, c i=0) :
    (∑ i, ∑ j, conj (c i)*c j*(1-radialOverlap k i j)).re ≤ 0 := by
  rw [complement_zero_sum k c hc]
  exact neg_nonpos.mpr (sq_nonneg _)

theorem radialOverlap_zero_one (k : ℕ) :
    radialOverlap k 0 1=(2*Real.sqrt 2/3 : ℝ) := by
  rw [radialOverlap_closed]
  norm_num
  ring

/-- The order-one old binomial stencil really detects the off-diagonal
correction; shrinking the grid never annihilates it. -/
theorem first_stencil_complement (k : ℕ) :
    (∑ i : Fin 2, ∑ j : Fin 2,
      conj (![(-1 : ℂ),1] i)*(![(-1 : ℂ),1] j)*
        (1-radialOverlap k i j)).re = -2+4*Real.sqrt 2/3 := by
  have h10 : radialOverlap k 1 0=radialOverlap k 0 1 := by
    rw [radialOverlap_closed,radialOverlap_closed]
    norm_num
    ring
  simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
    radialOverlap_diagonal]
  norm_num only [Fin.val_zero,Fin.val_one,map_neg,map_one,neg_mul,one_mul,
    mul_one,neg_neg,Complex.add_re,Complex.neg_re,Complex.sub_re,Complex.one_re]
  rw [h10,radialOverlap_zero_one]
  norm_num [Complex.mul_re,Complex.mul_im]
  ring

theorem first_stencil_complement_neg (k : ℕ) :
    (∑ i : Fin 2, ∑ j : Fin 2,
      conj (![(-1 : ℂ),1] i)*(![(-1 : ℂ),1] j)*
        (1-radialOverlap k i j)).re < 0 := by
  rw [first_stencil_complement]
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  nlinarith [Real.sqrt_nonneg (2 : ℝ)]

end
end CarryJetOverlap
