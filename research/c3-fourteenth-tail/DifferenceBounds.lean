import C3Difference

namespace CarryC3Tail
open CarrySelfAdjointOperator PhysicalSewing
open Set Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

theorem hasDerivAt_fd (n : ℕ) (f g : ℝ → ℂ) (a : ℝ)
    (h : ∀ x ∈ Icc a (a+n), HasDerivAt f (g x) x) :
    HasDerivAt (fd n f) (fd n g a) a := by
  induction n generalizing a with
  | zero => exact h a ⟨le_rfl,by simp⟩
  | succ n ih =>
    have h0 := ih a (fun x hx => h x ⟨hx.1,by push_cast; linarith [hx.2]⟩)
    have h1 := ih (a+1) (fun x hx => h x ⟨by linarith [hx.1],by push_cast; linarith [hx.2]⟩)
    have hs := h1.scomp a ((hasDerivAt_id a).add_const 1)
    have he : fd (n+1) f=(fun x : ℝ => fd n f (x+1)-fd n f x) := funext (fd_succ n f)
    rw [he]
    simpa only [fd_succ,Function.comp_def,id_eq,one_smul] using! hs.sub h0

/-- Complex-valued finite-difference bound, from the full derivative chain.
No complex mean-value equality, scalar projection, or sign premise is used. -/
theorem fd_norm_le (n : ℕ) (D : ℕ → ℝ → ℂ) (a C : ℝ)
    (hD : ∀ j < n, ∀ x ∈ Icc a (a+n), HasDerivAt (D j) (D (j+1) x) x)
    (hb : ∀ x ∈ Icc a (a+n), ‖D n x‖ ≤ C) : ‖fd n (D 0) a‖ ≤ C := by
  induction n generalizing D a with
  | zero => exact hb a ⟨le_rfl,by simp⟩
  | succ n ih =>
    have hmem (x : ℝ) (hx : x ∈ Icc a (a+1)) (y : ℝ) (hy : y ∈ Icc x (x+n)) :
        y ∈ Icc a (a+(n+1:ℕ)) := by
      constructor
      · linarith [hx.1,hy.1]
      · push_cast
        linarith [hx.2,hy.2]
    have hg (x : ℝ) (hx : x ∈ Icc a (a+1)) :
        HasDerivAt (fd n (D 0)) (fd n (D 1) x) x := by
      exact hasDerivAt_fd n _ _ x (fun y hy => hD 0 (by omega) y (hmem x hx y hy))
    have hgBound (x : ℝ) (hx : x ∈ Icc a (a+1)) : ‖fd n (D 1) x‖ ≤ C := by
      apply ih (fun j => D (j+1)) x
      · intro j hj y hy
        exact hD (j+1) (by omega) y (hmem x hx y hy)
      · intro y hy
        exact hb y (hmem x hx y hy)
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun x hx => (hg x hx).hasDerivWithinAt) hgBound (convex_Icc a (a+1))
      (by constructor <;> linarith : a ∈ Icc a (a+1))
      (by constructor <;> linarith : a+1 ∈ Icc a (a+1))
    simpa only [fd_succ,show a+1-a=1 by ring,norm_one,mul_one] using h

def falling (z : ℂ) (n : ℕ) : ℂ := ∏ j ∈ Finset.range n, (z-j)

theorem falling_succ (z : ℂ) (n : ℕ) : falling z (n+1)=falling z n*(z-n) := by
  exact Finset.prod_range_succ _ _

theorem falling_norm_le (z : ℂ) (hz : ‖z‖ ≤ 1) (n : ℕ) :
    ‖falling z n‖ ≤ (n.factorial:ℝ) := by
  induction n with
  | zero => simp [falling]
  | succ n ih =>
    have hn : ‖z-(n:ℂ)‖ ≤ (n+1:ℕ) := by
      have h := norm_sub_le z (n:ℂ)
      norm_num at h ⊢
      linarith
    rw [falling_succ,norm_mul,Nat.factorial_succ,Nat.cast_mul]
    calc
      ‖falling z n‖*‖z-(n:ℂ)‖ ≤ (n.factorial:ℝ)*(n+1:ℕ) :=
        mul_le_mul ih hn (norm_nonneg _) (by positivity)
      _ = _ := by ring

theorem cpow_derivative_chain (z : ℂ) (n : ℕ) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => falling z n*(y:ℂ)^(z-n))
      (falling z (n+1)*(x:ℂ)^(z-(n+1:ℕ))) x := by
  have h := (CarryFourthTail.cpow_spatial_derivative (z-n) x hx).const_mul (falling z n)
  have he : z-(n+1:ℕ)=z-(n:ℂ)-1 := by push_cast; ring
  rw [falling_succ,he]
  simpa only [mul_assoc] using h

theorem fd_cpow_norm_le (n : ℕ) (z : ℂ) (hz : ‖z‖ ≤ 1) (hre : z.re ≤ 0)
    (a : ℝ) (ha : 1 ≤ a) :
    ‖fd n (fun x : ℝ => (x:ℂ)^z) a‖ ≤ (n.factorial:ℝ)/a^n := by
  let D : ℕ → ℝ → ℂ := fun j x => falling z j*(x:ℂ)^(z-j)
  have hD : ∀ j < n, ∀ x ∈ Icc a (a+n), HasDerivAt (D j) (D (j+1) x) x := by
    intro j hj x hx
    exact cpow_derivative_chain z j x (by linarith [hx.1])
  have hb (x : ℝ) (hx : x ∈ Icc a (a+n)) : ‖D n x‖ ≤ (n.factorial:ℝ)/a^n := by
    have hx0 : 0 < x := by linarith [hx.1]
    have ha0 : 0 < a := by linarith
    have he : (z-(n:ℂ)).re ≤ -(n:ℝ) := by simp only [Complex.sub_re,Complex.natCast_re]; linarith
    have hp := (Real.rpow_le_rpow_of_exponent_le (ha.trans hx.1) he).trans
      (Real.rpow_le_rpow_of_nonpos ha0 hx.1 (neg_nonpos.mpr (Nat.cast_nonneg n)))
    dsimp only [D]
    rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have h := mul_le_mul (falling_norm_le z hz n) hp (Real.rpow_nonneg hx0.le _) (by positivity)
    simpa only [Real.rpow_neg ha0.le,Real.rpow_natCast,div_eq_mul_inv] using h
  have h := fd_norm_le n D a ((n.factorial:ℝ)/a^n) hD hb
  simpa only [D,falling,Finset.range_zero,Finset.prod_empty,Nat.cast_zero,sub_zero,one_mul] using h

theorem fd_nat_real (n : ℕ) (f : ℝ → ℂ) (a : ℕ) :
    fd n (fun k : ℕ => f k) a = fd n f (a:ℝ) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [fd_succ,fd_succ,ih,ih]
    simp only [Nat.cast_add,Nat.cast_one]

theorem c3_exponent_bounds (w : ℂ) (hw : ‖w‖ ≤ (1/2:ℝ)) :
    ‖-operatorHeightParameter w‖ ≤ 1 ∧ (-operatorHeightParameter w).re ≤ 0 := by
  have hn := norm_add_le (1/2:ℂ) (Complex.I*w)
  norm_num [norm_mul] at hn
  have hi := Complex.im_le_norm w
  constructor
  · simp only [norm_neg,operatorHeightParameter]
    linarith
  · norm_num [operatorHeightParameter,Complex.mul_re]
    linarith

theorem native_fd_bound (n a : ℕ) (ha : 0 < a) (w : ℂ) (hw : ‖w‖ ≤ (1/2:ℝ)) :
    ‖fd n (fun k => c3Sample k w) a‖ ≤ (n.factorial:ℝ)/(a:ℝ)^n := by
  obtain ⟨hn,hr⟩ := c3_exponent_bounds w hw
  unfold c3Sample
  have he := fd_nat_real n (fun x : ℝ => (x:ℂ)^(-operatorHeightParameter w)) a
  simp only [Complex.ofReal_natCast] at he
  rw [he]
  exact fd_cpow_norm_le n _ hn hr a (by exact_mod_cast ha)

theorem c3_sample_entire (a : ℕ) (ha : 0 < a) : Differentiable ℂ (c3Sample a) := by
  have he : c3Sample a=CarryFourthTail.complexSample a := funext (c3_sample_eq_generic_power a)
  rw [he]
  exact CarryFourthTail.complex_sample_entire a ha

theorem native_fd_entire (n a : ℕ) (ha : 0 < a) :
    Differentiable ℂ (fun w => fd n (fun k => c3Sample k w) a) := by
  induction n generalizing a with
  | zero => exact c3_sample_entire a ha
  | succ n ih =>
    simp only [fd_succ]
    exact (ih (a+1) (by omega)).sub (ih a ha)

end
end CarryC3Tail
