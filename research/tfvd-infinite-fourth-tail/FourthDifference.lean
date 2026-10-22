import TailAcceleration

/-! Quantitative fourth difference of the ORIGINAL complex-time material
sample. The whole stencil is differentiated before any norm is taken. -/
namespace CarryFourthTail
open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.BaseTwoCompletion
open CarryCellTail Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

theorem cpow_spatial_derivative (z : ℂ) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => (y:ℂ)^z) (z*(x:ℂ)^(z-1)) x := by
  by_cases hz : z = 0
  · subst z; simpa using (hasDerivAt_const x (1:ℂ))
  · exact hasDerivAt_ofReal_cpow_const (ne_of_gt hx) hz

/-- Two consecutive uses of the preexisting complete second-difference
estimate, keeping all five nodes of the resulting fourth difference. -/
theorem fourth_difference_norm_le (f f1 f2 f3 f4 : ℝ → ℂ) (a C : ℝ)
    (h0 : ∀ x ∈ Set.Icc a (a+4), HasDerivAt f (f1 x) x)
    (h1 : ∀ x ∈ Set.Icc a (a+4), HasDerivAt f1 (f2 x) x)
    (h2 : ∀ x ∈ Set.Icc a (a+4), HasDerivAt f2 (f3 x) x)
    (h3 : ∀ x ∈ Set.Icc a (a+4), HasDerivAt f3 (f4 x) x)
    (hb : ∀ x ∈ Set.Icc a (a+4), ‖f4 x‖ ≤ C) :
    ‖f (a+4)-4*f (a+3)+6*f (a+2)-4*f (a+1)+f a‖ ≤ C := by
  have hstep (g g1 : ℝ → ℂ)
      (hg : ∀ x ∈ Set.Icc a (a+4), HasDerivAt g (g1 x) x)
      (x : ℝ) (hx : x ∈ Set.Icc a (a+2)) :
      HasDerivAt (fun y => g (y+2)-2*g (y+1)+g y)
        (g1 (x+2)-2*g1 (x+1)+g1 x) x := by
    have ht (r : ℝ) (hr : 0 ≤ r) (hr2 : r ≤ 2) :
        HasDerivAt (fun y => g (y+r)) (g1 (x+r)) x := by
      have hm : x+r ∈ Set.Icc a (a+4) := by constructor <;> linarith [hx.1,hx.2]
      simpa only [Function.comp_def, id_eq, one_smul] using
        (hg (x+r) hm).scomp x ((hasDerivAt_id x).add_const r)
    exact ((ht 2 (by norm_num) le_rfl).sub ((ht 1 (by norm_num) (by norm_num)).const_mul 2)).add
      (hg x (by constructor <;> linarith [hx.1,hx.2]))
  have hinner (x : ℝ) (hx : x ∈ Set.Icc a (a+2)) :
      ‖f2 (x+2)-2*f2 (x+1)+f2 x‖ ≤ C := by
    have hm (y : ℝ) (hy : y ∈ Set.Icc x (x+2)) : y ∈ Set.Icc a (a+4) := by
      constructor <;> linarith [hx.1,hx.2,hy.1,hy.2]
    exact baseTwoSecondDifference_norm_le f2 f3 f4 x C
      (fun y hy => h2 y (hm y hy)) (fun y hy => h3 y (hm y hy)) (fun y hy => hb y (hm y hy))
  have h := baseTwoSecondDifference_norm_le
    (fun x => f (x+2)-2*f (x+1)+f x)
    (fun x => f1 (x+2)-2*f1 (x+1)+f1 x)
    (fun x => f2 (x+2)-2*f2 (x+1)+f2 x) a C
    (hstep f f1 h0) (hstep f1 f2 h1) hinner
  have he : (f (a+2+2)-2*f (a+2+1)+f (a+2))-
      2*(f (a+1+2)-2*f (a+1+1)+f (a+1))+(f (a+2)-2*f (a+1)+f a) =
      f (a+4)-4*f (a+3)+6*f (a+2)-4*f (a+1)+f a := by
    rw [show a+2+2=a+4 by ring, show a+2+1=a+3 by ring,
      show a+1+2=a+3 by ring, show a+1+1=a+2 by ring]
    ring
  exact he ▸ h

def complexSample (n : ℕ) (w : ℂ) : ℂ := (n:ℂ)^baseTwoComplexMaterialExponent w

theorem complex_sample_real (n : ℕ) (hn : 0 < n) (t : ℝ) :
    complexSample n (t:ℂ) = criticalMaterialSample t n :=
  (criticalMaterialSample_eq_cpow t hn).symm

theorem complex_sample_entire (n : ℕ) (hn : 0 < n) : Differentiable ℂ (complexSample n) := by
  have he : Differentiable ℂ baseTwoComplexMaterialExponent := by
    unfold baseTwoComplexMaterialExponent; fun_prop
  exact he.const_cpow (Or.inl (by exact_mod_cast (Nat.ne_of_gt hn)))

def complexFourth (a : ℕ) (w : ℂ) : ℂ := delta4 (fun n => complexSample n w) a
def complexBoundary (a : ℕ) (w : ℂ) : ℂ := tailBoundary (fun n => complexSample n w) a
def complexRemainder (a : ℕ) (w : ℂ) : ℂ := tailRemainder (fun n => complexSample n w) a

theorem complex_fourth_entire (a : ℕ) (ha : 0 < a) : Differentiable ℂ (complexFourth a) := by
  unfold complexFourth delta4
  exact ((((complex_sample_entire _ (by omega)).sub
    ((complex_sample_entire _ (by omega)).const_mul 4)).add
    ((complex_sample_entire _ (by omega)).const_mul 6)).sub
    ((complex_sample_entire _ (by omega)).const_mul 4)).add (complex_sample_entire a ha)

theorem exponent_closed_half (w : ℂ) (hw : ‖w‖ ≤ (1/2:ℝ)) :
    (baseTwoComplexMaterialExponent w).re ≤ 0 ∧ ‖baseTwoComplexMaterialExponent w‖ ≤ 1 := by
  constructor
  · have hi := Complex.im_le_norm w
    norm_num [baseTwoComplexMaterialExponent, Complex.mul_re]
    linarith
  · have h := norm_sub_le (-1/2:ℂ) (w*Complex.I)
    norm_num [norm_mul] at h
    unfold baseTwoComplexMaterialExponent
    linarith

theorem complex_fourth_bound (a : ℕ) (ha : 0 < a) (w : ℂ) (hw : ‖w‖ ≤ (1/2:ℝ)) :
    ‖complexFourth a w‖ ≤ 24/(a:ℝ)^4 := by
  let z := baseTwoComplexMaterialExponent w
  have ha0 : (0:ℝ) < a := by exact_mod_cast ha
  have ha1 : (1:ℝ) ≤ a := by exact_mod_cast ha
  obtain ⟨hre,hz⟩ := exponent_closed_half w hw
  have hz1 : ‖z-1‖ ≤ 2 := by have h := norm_sub_le z 1; norm_num at h; linarith
  have hz2 : ‖z-2‖ ≤ 3 := by have h := norm_sub_le z 2; norm_num at h; linarith
  have hz3 : ‖z-3‖ ≤ 4 := by have h := norm_sub_le z 3; norm_num at h; linarith
  have hp : ‖z*(z-1)*(z-2)*(z-3)‖ ≤ 24 := by
    simp only [norm_mul]
    calc
      ‖z‖*‖z-1‖*‖z-2‖*‖z-3‖ ≤ 1*2*3*4 := by gcongr
      _ = 24 := by norm_num
  have hb (x : ℝ) (hx : x ∈ Set.Icc (a:ℝ) (a+4)) :
      ‖z*(z-1)*(z-2)*(z-3)*(x:ℂ)^(z-4)‖ ≤ 24/(a:ℝ)^4 := by
    have hx0 := ha0.trans_le hx.1
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have he : (z-4).re ≤ (-4:ℝ) := by simp only [Complex.sub_re]; norm_num; exact hre
    have hpow := (Real.rpow_le_rpow_of_exponent_le (ha1.trans hx.1) he).trans
      (Real.rpow_le_rpow_of_nonpos ha0 hx.1 (by norm_num))
    have h := mul_le_mul hp hpow (Real.rpow_nonneg hx0.le _) (by norm_num : (0:ℝ) ≤ 24)
    simpa only [Real.rpow_neg ha0.le, Real.rpow_natCast, Real.rpow_ofNat, div_eq_mul_inv] using h
  have h := fourth_difference_norm_le
    (fun x => (x:ℂ)^z) (fun x => z*(x:ℂ)^(z-1))
    (fun x => z*(z-1)*(x:ℂ)^(z-2))
    (fun x => z*(z-1)*(z-2)*(x:ℂ)^(z-3))
    (fun x => z*(z-1)*(z-2)*(z-3)*(x:ℂ)^(z-4)) (a:ℝ) (24/(a:ℝ)^4)
    (fun x hx => cpow_spatial_derivative z x (ha0.trans_le hx.1))
    (by intro x hx; simpa only [show z-1-1=z-2 by ring, mul_assoc] using
      (cpow_spatial_derivative (z-1) x (ha0.trans_le hx.1)).const_mul z)
    (by intro x hx; simpa only [show z-2-1=z-3 by ring, mul_assoc] using
      (cpow_spatial_derivative (z-2) x (ha0.trans_le hx.1)).const_mul (z*(z-1)))
    (by intro x hx; simpa only [show z-3-1=z-4 by ring, mul_assoc] using
      (cpow_spatial_derivative (z-3) x (ha0.trans_le hx.1)).const_mul (z*(z-1)*(z-2))) hb
  convert h using 1
  simp only [complexFourth, delta4, complexSample, z, Nat.cast_add,
    Nat.cast_ofNat, Nat.cast_one, Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_ofNat, Complex.ofReal_one]
end
end CarryFourthTail
