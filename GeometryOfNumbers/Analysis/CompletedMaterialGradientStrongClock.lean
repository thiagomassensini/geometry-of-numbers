import GeometryOfNumbers.Analysis.BaseTwoCompletedBoundaryDynamics
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-! # Strong material-gradient clock

Uniform spatial first-difference estimates prove convergence of the vector
series in the standard lp spaces before differentiation. Coordinate derivative
laws are used only after strong differentiability has been established.
-/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators lp ENNReal
namespace GeometryOfNumbers.Analysis.BaseTwoCompletion

/-- Auxiliary complex-time continuation of the existing material gradient.
This is not a complex Taylor product-ledger state. -/
def baseTwoComplexMaterialGradient (w : ℂ) (j : ℕ) : ℂ :=
  ((j+2 : ℕ):ℂ)^baseTwoComplexMaterialExponent w -
    ((j+1 : ℕ):ℂ)^baseTwoComplexMaterialExponent w

theorem baseTwoComplexMaterialGradient_ofReal (t : ℝ) (j : ℕ) :
    baseTwoComplexMaterialGradient (t:ℂ) j = criticalMaterialGradient t j := by
  rw [baseTwoComplexMaterialGradient, criticalMaterialGradient,
    criticalMaterialSample_eq_cpow t (by omega), criticalMaterialSample_eq_cpow t (by omega)]
  rfl

private theorem complexGradient_differentiable (j : ℕ) :
    Differentiable ℂ (fun w => baseTwoComplexMaterialGradient w j) := by
  have he : Differentiable ℂ baseTwoComplexMaterialExponent := by
    unfold baseTwoComplexMaterialExponent; fun_prop
  have h1 : ((j+1 : ℕ):ℂ) ≠ 0 := by exact_mod_cast (show j+1 ≠ 0 by omega)
  have h2 : ((j+2 : ℕ):ℂ) ≠ 0 := by exact_mod_cast (show j+2 ≠ 0 by omega)
  exact (he.const_cpow (Or.inl h2)).sub (he.const_cpow (Or.inl h1))

/-- Uniform norm majorant for whole gradient vectors near every real time. -/
theorem baseTwoComplexMaterialGradient_norm_le (t : ℝ) (j : ℕ) (w : ℂ)
    (hw : w ∈ Metric.ball (t:ℂ) (1/4:ℝ)) :
    ‖baseTwoComplexMaterialGradient w j‖ ≤
      (|t|+2)*((j+1:ℕ):ℝ)^(-5/4:ℝ) := by
  let z := baseTwoComplexMaterialExponent w
  let a : ℝ := (j+1 : ℕ)
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : 1 ≤ a := by dsimp [a]; exact_mod_cast (Nat.succ_pos j)
  have hdist : ‖w-(t:ℂ)‖ < (1/4:ℝ) := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hw
  have hwNorm : ‖w‖ ≤ |t|+1 := by
    have h := norm_add_le (w-(t:ℂ)) (t:ℂ)
    rw [sub_add_cancel] at h
    simp only [Complex.norm_real, Real.norm_eq_abs] at h
    linarith
  have hwIm : w.im ≤ (1/4:ℝ) := by
    have h := Complex.im_le_norm (w-(t:ℂ))
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at h
    linarith
  have hzRe : z.re ≤ (-1/4:ℝ) := by
    norm_num [z, baseTwoComplexMaterialExponent, Complex.mul_re] at *
    linarith
  have hz : z ≠ 0 := by intro h; rw [h] at hzRe; norm_num at hzRe
  have hzNorm : ‖z‖ ≤ |t|+2 := by
    have h := norm_sub_le (-1/2:ℂ) (w*Complex.I)
    norm_num [norm_mul, Complex.norm_I] at h
    dsimp [z, baseTwoComplexMaterialExponent]
    linarith
  have hfun : baseTwoComplexMaterialGradient w j = ((a+1:ℝ):ℂ)^z-(a:ℂ)^z := by
    simp only [baseTwoComplexMaterialGradient, a, z, Nat.cast_add, Nat.cast_one,
      Nat.cast_ofNat, Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_natCast]
    congr 2; ring
  have hb : ∀ x ∈ Set.Icc a (a+1), ‖z*(x:ℂ)^(z-1)‖ ≤ (|t|+2)*a^(-5/4:ℝ) := by
    intro x hx
    have hxpos := lt_of_lt_of_le ha hx.1
    have hx1 : 1 ≤ x := ha1.trans hx.1
    have he : (z-1).re ≤ (-5/4:ℝ) := by simp only [Complex.sub_re, Complex.one_re]; linarith
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
    have hp : x^((z-1).re) ≤ a^(-5/4:ℝ) :=
      (Real.rpow_le_rpow_of_exponent_le hx1 he).trans
        (Real.rpow_le_rpow_of_nonpos ha hx.1 (by norm_num))
    exact mul_le_mul hzNorm hp (Real.rpow_nonneg hxpos.le _) (by positivity)
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (hasDerivAt_ofReal_cpow_const
      (ne_of_gt (lt_of_lt_of_le ha hx.1)) hz).hasDerivWithinAt)
    hb (convex_Icc a (a+1))
    (by constructor <;> linarith : a ∈ Set.Icc a (a+1))
    (by constructor <;> linarith : a+1 ∈ Set.Icc a (a+1))
  rw [hfun]
  simpa only [show a+1-a=(1:ℝ) by ring, norm_one, mul_one] using h

/-- The standard vector series of material edges, with no changed norm. -/
def baseTwoComplexMaterialGradientLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (w : ℂ) :
    lp (fun _ : ℕ => ℂ) p := ∑' j : ℕ, lp.single p j (baseTwoComplexMaterialGradient w j)

theorem baseTwoComplexMaterialGradientLp_differentiableOn_ball
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (t : ℝ) :
    DifferentiableOn ℂ (baseTwoComplexMaterialGradientLp p)
      (Metric.ball (t:ℂ) (1/4:ℝ)) := by
  have hp : Summable (fun j : ℕ => ((j+1:ℕ):ℝ)^(-5/4:ℝ)) :=
    (summable_nat_add_iff 1).2 (Real.summable_nat_rpow.mpr (by norm_num))
  exact Complex.differentiableOn_tsum_of_summable_norm (hp.mul_left (|t|+2))
    (fun j => (((lp.singleContinuousLinearMap ℂ (fun _ : ℕ => ℂ) p j).differentiable).comp
      (complexGradient_differentiable j)).differentiableOn) Metric.isOpen_ball
    (fun j w hw => by
      rw [lp.norm_single (zero_lt_one.trans_le Fact.out)]
      exact baseTwoComplexMaterialGradient_norm_le t j w hw)

theorem baseTwoComplexMaterialGradientLp_ofReal (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (t : ℝ) (g : lp (fun _ : ℕ => ℂ) p)
    (hg : ∀ j, g j = criticalMaterialGradient t j) :
    baseTwoComplexMaterialGradientLp p (t:ℂ) = g := by
  have he : (fun j => lp.single p j (baseTwoComplexMaterialGradient (t:ℂ) j)) =
      (fun j => lp.single (E := fun _ : ℕ => ℂ) p j (g j)) := by
    funext j; rw [baseTwoComplexMaterialGradient_ofReal, hg]
  rw [baseTwoComplexMaterialGradientLp, he]
  exact (lp.hasSum_single hp g).tsum_eq

private theorem realGradientLp_differentiableAt (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (g : ℝ → lp (fun _ : ℕ => ℂ) p)
    (hg : ∀ t j, g t j = criticalMaterialGradient t j) (t : ℝ) :
    DifferentiableAt ℝ g t := by
  have hC := (baseTwoComplexMaterialGradientLp_differentiableOn_ball p t).differentiableAt
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num)))
  have hR := (hC.restrictScalars ℝ).comp t Complex.ofRealCLM.differentiableAt
  have he : baseTwoComplexMaterialGradientLp p ∘ Complex.ofReal = g := by
    funext u
    exact baseTwoComplexMaterialGradientLp_ofReal p hp u (g u) (hg u)
  simpa only [Complex.ofRealCLM_apply, he] using hR

theorem baseTwoCompletedMaterialGradient_differentiableAt (t : ℝ) :
    DifferentiableAt ℝ baseTwoCompletedMaterialGradient t :=
  realGradientLp_differentiableAt 1 (by norm_num) _ (fun _ _ => rfl) t

theorem baseTwoCompletedMaterialGradientL2_differentiableAt (t : ℝ) :
    DifferentiableAt ℝ baseTwoCompletedMaterialGradientL2 t :=
  realGradientLp_differentiableAt 2 (by norm_num) _ (fun _ _ => rfl) t

/-- Strong derivative has the previously derived triangular clock coordinates. -/
theorem baseTwoCompletedMaterialGradient_deriv_apply (t : ℝ) (j : ℕ) :
    deriv baseTwoCompletedMaterialGradient t j =
      -Complex.I * baseTwoCompletedBoundaryHilbertClockCoordinate
        (baseTwoCompletedBoundaryHilbertState t) j := by
  have h := ((lp.evalCLM ℂ (fun _ : ℕ => ℂ) 1 j).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    (baseTwoCompletedMaterialGradient_differentiableAt t).hasDerivAt
  change HasDerivAt (fun u => baseTwoCompletedMaterialGradient u j)
    (deriv baseTwoCompletedMaterialGradient t j) t at h
  have he : (fun u => baseTwoCompletedMaterialGradient u j) =
      (fun u => criticalMaterialGradient u j) := rfl
  rw [he] at h
  have hv := h.unique (criticalMaterialGradient_hasDerivAt t j)
  simpa only [baseTwoCompletedBoundaryHilbertClockCoordinate_eq] using hv

theorem baseTwoCompletedMaterialGradientL2_deriv_apply (t : ℝ) (j : ℕ) :
    deriv baseTwoCompletedMaterialGradientL2 t j =
      -Complex.I * baseTwoCompletedBoundaryHilbertClockCoordinate
        (baseTwoCompletedBoundaryHilbertState t) j := by
  have h := ((lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 j).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    (baseTwoCompletedMaterialGradientL2_differentiableAt t).hasDerivAt
  change HasDerivAt (fun u => baseTwoCompletedMaterialGradientL2 u j)
    (deriv baseTwoCompletedMaterialGradientL2 t j) t at h
  have he : (fun u => baseTwoCompletedMaterialGradientL2 u j) =
      (fun u => criticalMaterialGradient u j) := rfl
  rw [he] at h
  have hv := h.unique (criticalMaterialGradient_hasDerivAt t j)
  simpa only [baseTwoCompletedBoundaryHilbertClockCoordinate_eq] using hv


/-- The triangular coordinates of the concrete orbit are absolutely summable,
proved from the strong ℓ¹ derivative, not from coordinatewise differentiation. -/
theorem baseTwoCompletedMaterialClock_memLp_one (t : ℝ) :
    Memℓp (fun j => baseTwoCompletedBoundaryHilbertClockCoordinate
      (baseTwoCompletedBoundaryHilbertState t) j) 1 := by
  have he : (fun j => baseTwoCompletedBoundaryHilbertClockCoordinate
      (baseTwoCompletedBoundaryHilbertState t) j) =
      ⇑(Complex.I • deriv baseTwoCompletedMaterialGradient t) := by
    funext j
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
      baseTwoCompletedMaterialGradient_deriv_apply]
    rw [neg_mul, mul_neg, ← mul_assoc, Complex.I_mul_I]
    simp
  rw [he]
  exact lp.memℓp _

def baseTwoCompletedMaterialClockL1 (t : ℝ) : MaterialGradientL1 :=
  ⟨_, baseTwoCompletedMaterialClock_memLp_one t⟩

def baseTwoCompletedMaterialClockL2 (t : ℝ) : MaterialEdgeL2 :=
  ⟨_, (baseTwoCompletedMaterialClock_memLp_one t).of_exponent_ge (by norm_num)⟩

@[simp] theorem baseTwoCompletedMaterialClockL1_apply (t : ℝ) (j : ℕ) :
    baseTwoCompletedMaterialClockL1 t j = baseTwoCompletedBoundaryHilbertClockCoordinate
      (baseTwoCompletedBoundaryHilbertState t) j := rfl

@[simp] theorem baseTwoCompletedMaterialClockL2_apply (t : ℝ) (j : ℕ) :
    baseTwoCompletedMaterialClockL2 t j = baseTwoCompletedBoundaryHilbertClockCoordinate
      (baseTwoCompletedBoundaryHilbertState t) j := rfl

theorem baseTwoCompletedMaterialGradient_hasDerivAt_clock (t : ℝ) :
    HasDerivAt baseTwoCompletedMaterialGradient
      (-Complex.I • baseTwoCompletedMaterialClockL1 t) t := by
  have he : deriv baseTwoCompletedMaterialGradient t =
      -Complex.I • baseTwoCompletedMaterialClockL1 t := by
    apply lp.ext; funext j
    exact baseTwoCompletedMaterialGradient_deriv_apply t j
  rw [← he]
  exact (baseTwoCompletedMaterialGradient_differentiableAt t).hasDerivAt

theorem baseTwoCompletedMaterialGradientL2_hasDerivAt_clock (t : ℝ) :
    HasDerivAt baseTwoCompletedMaterialGradientL2
      (-Complex.I • baseTwoCompletedMaterialClockL2 t) t := by
  have he : deriv baseTwoCompletedMaterialGradientL2 t =
      -Complex.I • baseTwoCompletedMaterialClockL2 t := by
    apply lp.ext; funext j
    exact baseTwoCompletedMaterialGradientL2_deriv_apply t j
  rw [← he]
  exact (baseTwoCompletedMaterialGradientL2_differentiableAt t).hasDerivAt

/-- Actual clocked cell returns, not a definition via derivative of the signal. -/
def baseTwoCompletedBoundaryClockReturn (y : BaseTwoCompletedBoundaryHilbertCarrier) : ℂ :=
  ∑' k : ℕ, (baseTwoCompletedBoundaryHilbertClockCoordinate y (baseTwoCellRightEdge k) -
    baseTwoCompletedBoundaryHilbertClockCoordinate y (baseTwoCellLeftEdge k))

theorem summable_baseTwoCompletedBoundaryClockReturn (t : ℝ) :
    Summable (fun k =>
      baseTwoCompletedBoundaryHilbertClockCoordinate (baseTwoCompletedBoundaryHilbertState t)
        (baseTwoCellRightEdge k) -
      baseTwoCompletedBoundaryHilbertClockCoordinate (baseTwoCompletedBoundaryHilbertState t)
        (baseTwoCellLeftEdge k)) := by
  have hn : Summable (fun j => ‖baseTwoCompletedMaterialClockL1 t j‖) := by
    simpa using (baseTwoCompletedMaterialClockL1 t).property.summable
  have hs := hn.of_norm
  exact (hs.comp_injective (by intro i j h; simp at h; omega :
    Function.Injective baseTwoCellRightEdge)).sub
    (hs.comp_injective (by intro i j h; simp at h; omega :
      Function.Injective baseTwoCellLeftEdge))

/-- Boundary differentiation factors through the preexisting ℓ¹ cell-return
readout and the strong vector derivative. -/
theorem baseTwoCompletedBoundaryValue_hasDerivAt_clock (t : ℝ) :
    HasDerivAt baseTwoCompletedBoundaryValue
      (-Complex.I * baseTwoCompletedBoundaryClockReturn
        (baseTwoCompletedBoundaryHilbertState t)) t := by
  let beta : MaterialGradientL1 →L[ℂ] ℂ := baseTwoCompletedUndressedReadout.comp
    (ContinuousLinearMap.inr ℂ ℂ MaterialGradientL1)
  have he : (fun u => beta (baseTwoCompletedMaterialGradient u)) =
      baseTwoCompletedBoundaryValue := by
    funext u
    change baseTwoCompletedUndressedReadout (0, baseTwoCompletedMaterialGradient u) = _
    rw [baseTwoCompletedUndressedReadout_apply]
    simp only [zero_add, baseTwoCompletedMaterialGradient_apply]
    rfl
  have hv : beta (-Complex.I • baseTwoCompletedMaterialClockL1 t) =
      -Complex.I * baseTwoCompletedBoundaryClockReturn (baseTwoCompletedBoundaryHilbertState t) := by
    rw [map_smul]
    change -Complex.I * baseTwoCompletedUndressedReadout (0, baseTwoCompletedMaterialClockL1 t) = _
    rw [baseTwoCompletedUndressedReadout_apply]
    simp only [zero_add, baseTwoCompletedMaterialClockL1_apply, baseTwoCompletedBoundaryClockReturn]
  have h := (beta.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    (baseTwoCompletedMaterialGradient_hasDerivAt_clock t)
  change HasDerivAt (fun u => beta (baseTwoCompletedMaterialGradient u))
    (beta (-Complex.I • baseTwoCompletedMaterialClockL1 t)) t at h
  rwa [he, hv] at h

end GeometryOfNumbers.Analysis.BaseTwoCompletion
