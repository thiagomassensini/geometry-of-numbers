import SourceComputation
import ThetaRetainedTail
import CodeBounds

/-! Every box below reads the original theta modes. They are numerical
proof enclosures, never replacement sources or altered normalizations. -/
namespace CarryIntegralCertificate
open CarrySelfAdjointOperator Real Polynomial
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem mem_ofRat (q : ℚ) : (Box.ofRat q).Mem (q:ℝ) := by
  change (Box.rat q.num q.den).Mem (q:ℝ)
  simpa only [Rat.cast_def,Int.cast_natCast] using mem_rat q.num q.den

theorem mem_piBox : piBox.Mem Real.pi := by
  apply mem_outer (mem_rat _ _) (mem_rat _ _)
  · norm_num only [Int.cast_ofNat,Int.cast_pow]
    linarith [Real.pi_gt_d20]
  · norm_num only [Int.cast_ofNat,Int.cast_pow]
    linarith [Real.pi_lt_d20]

theorem mem_argumentBox (m : ℕ) {a : Box} {x : ℝ} (hx : a.Mem x) :
    (argumentBox m a).Mem (thetaArgument m x) := by
  have h := mem_mul (mem_mul mem_piBox (mem_pow (mem_point ((m+1:ℕ):ℤ)) 2))
    (mem_exp (mem_mul hx (mem_point 2)))
  simpa only [argumentBox,thetaArgument,Int.cast_natCast,Int.cast_ofNat,mul_comm x 2] using h

theorem mem_modeBox (m : ℕ) {a : Box} {x : ℝ} (hx : a.Mem x) :
    (modeBox m a).Mem (thetaMode m x) := by
  have h := mem_div (mem_mul (mem_point 2) (mem_exp (mem_div hx (mem_point 2))))
    (mem_exp (mem_argumentBox m hx))
  have he : thetaMode m x = 2*Real.exp (x/2)/Real.exp (thetaArgument m x) := by
    rw [thetaMode_eq_exp,Real.exp_sub]
    ring
  rw [he]
  simpa only [modeBox,Int.cast_ofNat] using h

theorem mem_polynomialBox (n : ℕ) (hn : n ≤ 16) {a : Box} {x : ℝ} (hx : a.Mem x) :
    (polynomialBox n a).Mem (aeval x (thetaDerivativePolynomial n)) := by
  rw [thetaCode_eval n hn]
  exact mem_sum _ _ _ (fun r _ => mem_mul (mem_ofRat _) (mem_pow hx r))

theorem mem_derivativeBox (m n : ℕ) (hn : n ≤ 16) {a : Box} {x : ℝ} (hx : a.Mem x) :
    (derivativeBox m n a).Mem (thetaModeDerivative m n x) :=
  mem_mul (mem_polynomialBox n hn (mem_argumentBox m hx)) (mem_modeBox m hx)

theorem mem_majorantBox (m n : ℕ) {b : Box} {x : ℝ} (hx : b.Mem x) :
    (majorantBox m n b).Mem (thetaCodeMajorant n (thetaArgument m x)) := by
  apply mem_sum
  intro r _
  have h := mem_mul (mem_ofRat |(thetaCoefficientCode n)[r]?.getD 0|)
    (mem_pow (mem_argumentBox m hx) r)
  simpa only [Rat.cast_abs] using h

theorem mem_powerMassBox (p r : ℕ) {a b : Box} {x y : ℝ}
    (hx : a.Mem x) (hy : b.Mem y) :
    (powerMassBox p r a b).Mem (weightedPowerMass p r x y) := by
  unfold powerMassBox
  rw [← Nat.choose_eq_fast_choose]
  apply mem_sum
  intro k _
  have h := mem_div (mem_mul (mem_mul (mem_point (p.choose k)) (mem_pow hx (p-k)))
    (mem_pow (mem_add hy (mem_neg hx)) (k+r+1))) (mem_point ((k+r+1:ℕ):ℤ))
  simpa only [Int.cast_natCast,Int.cast_add,Int.cast_one,Nat.cast_add,Nat.cast_one,sub_eq_add_neg] using h

theorem mem_taylorMassBox (m n p : ℕ) (hn : n ≤ 16) {a b : Box} {x y : ℝ}
    (hx : a.Mem x) (hy : b.Mem y) :
    (taylorMassBox m n p a b).Mem (weightedTaylorMass m n p x y) := by
  apply mem_sum
  intro r hr
  have h := mem_mul (mem_div (mem_derivativeBox m r (by omega) hx) (mem_point (r.factorial:ℤ)))
    (mem_powerMassBox p r hx hy)
  simpa only [derivativeBox,Int.cast_natCast] using h

theorem mem_cellBox (m n p : ℕ) (hn : n < 16) {a b : Box} {x y : ℝ}
    (hx : a.Mem x) (hy : b.Mem y) (hx0 : 0 ≤ x) (hxy : x < y) :
    (cellBox m n p a b).Mem (∫ u in x..y, u^p*thetaMode m u) := by
  have hv := mem_taylorMassBox m n p (by omega) hx hy
  have he := mem_mul (mem_div (mem_mul (mem_majorantBox m (n+1) hy) (mem_modeBox m hx))
    (mem_point (n.factorial:ℤ))) (mem_powerMassBox p (n+1) hx hy)
  simp only [Int.cast_natCast] at he
  have hbound := thetaMode_weighted_cell_bounds m n p x y _ hx0 hxy
    (thetaCode_cell_bound m (n+1) (by omega) x y hx0)
  apply mem_outer (mem_add hv (mem_neg he)) (mem_add hv he)
  · simpa only [sub_eq_add_neg] using hbound.1
  · exact hbound.2

end CarryIntegralCertificate
