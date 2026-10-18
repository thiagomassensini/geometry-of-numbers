import SourceTail

namespace CarrySourceTail
open CarrySelfAdjointOperator CarryCriticalSource CarryThetaPattern
open scoped BigOperators ComplexConjugate Matrix Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

/-- A full complex estimate, before extracting the real energy. -/
theorem sourcePair_diagonal_cutoff_weighted {N M : ℕ} (s : ℕ)
    (x : Fin N → ℂ) (a : Fin M → ℂ) :
    ‖sourcePair s (Fin.append x a) (Fin.append x a)-sourcePair s x x‖ ≤
      rate^(s+1)*(2*rate^N*weightedSize x*weightedSize a+
        rate^(2*N)*weightedSize a^2) := by
  rw [sourcePair_append]
  have he : sourcePair s x x+sourcePair (s+N) x a+
      sourcePair (s+N) a x+sourcePair (s+2*N) a a-sourcePair s x x =
        sourcePair (s+N) x a+sourcePair (s+N) a x+sourcePair (s+2*N) a a := by ring
  rw [he]
  calc
    _ ≤ ‖sourcePair (s+N) x a‖+‖sourcePair (s+N) a x‖+
        ‖sourcePair (s+2*N) a a‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ rate^(s+N+1)*weightedSize x*weightedSize a+
        rate^(s+N+1)*weightedSize a*weightedSize x+
        rate^(s+2*N+1)*weightedSize a*weightedSize a :=
      add_le_add (add_le_add (sourcePair_norm_le _ _ _) (sourcePair_norm_le _ _ _))
        (sourcePair_norm_le _ _ _)
    _ = _ := by
      rw [show s+N+1=(s+1)+N by omega, show s+2*N+1=(s+1)+2*N by omega,
        pow_add, pow_add]
      ring

/-- UNCONDITIONAL in both cutoff and remaining order. Every head/tail
crossing is estimated from the literal synthesized source, not discarded. -/
theorem sourcePair_diagonal_cutoff_bound {N M : ℕ} (s : ℕ)
    (x : Fin N → ℂ) (a : Fin M → ℂ) :
    ‖sourcePair s (Fin.append x a) (Fin.append x a)-sourcePair s x x‖ ≤
      cutoffError s N*(coefficientEnergy x+coefficientEnergy a) := by
  have hx := weightedSize_sq_le x
  have ha := weightedSize_sq_le a
  have hcross : 2*rate^N*weightedSize x*weightedSize a+
      rate^(2*N)*weightedSize a^2 ≤
        (rate^N+rate^(2*N))*(weightedSize x^2+weightedSize a^2) := by
    nlinarith [mul_nonneg (pow_nonneg rate_pos.le N)
      (sq_nonneg (weightedSize x-weightedSize a)),
      mul_nonneg (pow_nonneg rate_pos.le (2*N)) (sq_nonneg (weightedSize x))]
  calc
    _ ≤ rate^(s+1)*(2*rate^N*weightedSize x*weightedSize a+
        rate^(2*N)*weightedSize a^2) := sourcePair_diagonal_cutoff_weighted s x a
    _ ≤ rate^(s+1)*((rate^N+rate^(2*N))*(weightedSize x^2+weightedSize a^2)) :=
      mul_le_mul_of_nonneg_left hcross (pow_nonneg rate_pos.le _)
    _ ≤ rate^(s+1)*((rate^N+rate^(2*N))*
        (coefficientEnergy x/(1-rate^2)+coefficientEnergy a/(1-rate^2))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (add_le_add hx ha) (by positivity [rate_pos.le]))
        (pow_nonneg rate_pos.le _)
    _ = _ := by unfold cutoffError; ring

def sourceRealPair {n m : ℕ} (s : ℕ) (x : Fin n → ℝ) (y : Fin m → ℝ) : ℝ :=
  ∑ i, ∑ j, h (i.val+j.val+s)*x i*y j

/-- Two independently polarized real quadratures, including their ordered
symplectic complement. These are not a new complex-linear equivalence. -/
theorem sourcePair_re {n m : ℕ} (s : ℕ) (x : Fin n → ℂ) (y : Fin m → ℂ) :
    (sourcePair s x y).re =
      sourceRealPair s (fun i => (x i).re) (fun j => (y j).re)+
        sourceRealPair s (fun i => (x i).im) (fun j => (y j).im) := by
  simp only [sourcePair, sourceRealPair, Complex.re_sum, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
    zero_mul, add_zero, mul_neg, neg_mul, sub_neg_eq_add,
    Finset.sum_add_distrib]

theorem sourcePair_im {n m : ℕ} (s : ℕ) (x : Fin n → ℂ) (y : Fin m → ℂ) :
    (sourcePair s x y).im =
      sourceRealPair s (fun i => (x i).re) (fun j => (y j).im)-
        sourceRealPair s (fun i => (x i).im) (fun j => (y j).re) := by
  simp only [sourcePair, sourceRealPair, Complex.im_sum, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
    zero_mul, add_zero, neg_zero, mul_neg, neg_mul, sub_eq_add_neg,
    Finset.sum_add_distrib, Finset.sum_neg_distrib]

theorem sourceRealPair_self {n : ℕ} (s : ℕ) (x : Fin n → ℝ) :
    sourceRealPair s x x = sourceMomentQuadratic h s n x := by
  simp only [sourceRealPair, sourceMomentQuadratic, sourceMomentMatrix,
    dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem sourcePair_re_nonneg {n : ℕ} (s : ℕ)
    (hp : (sourceMomentMatrix h s n).PosSemidef) (x : Fin n → ℂ) :
    0 ≤ (sourcePair s x x).re := by
  rw [sourcePair_re, sourceRealPair_self, sourceRealPair_self]
  exact add_nonneg (hp.dotProduct_mulVec_nonneg _) (hp.dotProduct_mulVec_nonneg _)

/-- A certified finite prefix bounds possible negative energy in EVERY
larger order, but the right side is negative and is not a sign certificate. -/
theorem all_order_lower_bound_from_prefix {N M : ℕ} (s : ℕ)
    (hp : (sourceMomentMatrix h s N).PosSemidef)
    (x : Fin N → ℂ) (a : Fin M → ℂ) :
    -cutoffError s N*(coefficientEnergy x+coefficientEnergy a) ≤
      (sourcePair s (Fin.append x a) (Fin.append x a)).re := by
  have hb := sourcePair_diagonal_cutoff_bound s x a
  have hr := Complex.abs_re_le_norm
    (sourcePair s (Fin.append x a) (Fin.append x a)-sourcePair s x x)
  have hn := sourcePair_re_nonneg s hp x
  simp only [Complex.sub_re] at hr
  have hl := (abs_le.mp (hr.trans hb)).1
  linarith

/-- Fully source-backed, UNCONDITIONAL at arbitrary remaining order. -/
theorem all_order_lower_bound_from_certified_five (s : Fin 2) {M : ℕ}
    (x : Fin 5 → ℂ) (a : Fin M → ℂ) :
    -cutoffError s.val 5*(coefficientEnergy x+coefficientEnergy a) ≤
      (sourcePair s.val (Fin.append x a) (Fin.append x a)).re := by
  apply all_order_lower_bound_from_prefix
  fin_cases s
  · exact even_source_five_posDef.posSemidef
  · exact odd_source_five_posDef.posSemidef

theorem cutoffError_tendsto_zero (s : ℕ) :
    Filter.Tendsto (cutoffError s) Filter.atTop (nhds 0) := by
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one rate_pos.le rate_lt_one
  have h2 : Filter.Tendsto (fun N : ℕ => rate^(2*N)) Filter.atTop (nhds 0) := by
    simpa only [← pow_mul, Nat.mul_comm, zero_pow (by decide : 2 ≠ 0)] using ht.pow 2
  have hh := ((ht.add h2).const_mul (rate^(s+1))).div_const (1-rate^2)
  change Filter.Tendsto (fun N => rate^(s+1)*(rate^N+rate^(2*N))/(1-rate^2))
    Filter.atTop (nhds 0)
  simpa only [add_zero, mul_zero, zero_div] using hh

end
end CarrySourceTail
