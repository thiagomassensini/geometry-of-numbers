import ClockReturnJets
import Mathlib.Analysis.Complex.Liouville

/-! Quantitative estimates of the SAME complete native cells. The auxiliary
complex continuation changes neither the real source nor the physical metric. -/
namespace CarryCellTail
open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.BaseTwoCompletion
open CarryMaterialParts Filter Topology
open scoped BigOperators ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

def complexCell (k : ℕ) (w : ℂ) : ℂ :=
  baseTwoComplexMaterialGradient w (baseTwoCellRightEdge k)-
    baseTwoComplexMaterialGradient w (baseTwoCellLeftEdge k)

theorem complex_cell_real (k : ℕ) (t : ℝ) :
    complexCell k (t:ℂ) = baseTwoCriticalCenterCell t k := by
  rw [complexCell, baseTwoComplexMaterialGradient_ofReal,
    baseTwoComplexMaterialGradient_ofReal, baseTwoCriticalCenterCell_eq_gradientEdges]

theorem complex_cell_entire (k : ℕ) : Differentiable ℂ (complexCell k) := by
  have he : Differentiable ℂ baseTwoComplexMaterialExponent := by
    unfold baseTwoComplexMaterialExponent; fun_prop
  have hg (j : ℕ) : Differentiable ℂ (fun w => baseTwoComplexMaterialGradient w j) := by
    apply Differentiable.sub
    · exact he.const_cpow (Or.inl (by exact_mod_cast (show j+2 ≠ 0 by omega)))
    · exact he.const_cpow (Or.inl (by exact_mod_cast (show j+1 ≠ 0 by omega)))
  exact (hg _).sub (hg _)

/-- Second-difference cancellation is retained before taking any norm. -/
theorem complex_cell_bound (k : ℕ) (w : ℂ) (hw : ‖w‖ ≤ (1/2:ℝ)) :
    ‖complexCell k w‖ ≤ 2 / ((4*k+3:ℕ):ℝ)^2 := by
  let z := baseTwoComplexMaterialExponent w
  let a : ℝ := (4*k+3:ℕ)
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : 1 ≤ a := by dsimp [a]; norm_cast; omega
  have hre : z.re ≤ 0 := by
    have hi := Complex.im_le_norm w
    norm_num [z, baseTwoComplexMaterialExponent, Complex.mul_re]
    linarith
  have hz : ‖z‖ ≤ 1 := by
    have h := norm_sub_le (-1/2:ℂ) (w*Complex.I)
    norm_num [norm_mul] at h
    dsimp [z, baseTwoComplexMaterialExponent]
    linarith
  have hz1 : ‖z-1‖ ≤ 2 := by
    have h := norm_sub_le z 1
    norm_num at h
    linarith
  have hder (r : ℂ) (x : ℝ) (hx : 0 < x) :
      HasDerivAt (fun y : ℝ => (y:ℂ)^r) (r*(x:ℂ)^(r-1)) x := by
    by_cases hr : r = 0
    · subst r; simpa using (hasDerivAt_const x (1:ℂ))
    · exact hasDerivAt_ofReal_cpow_const (ne_of_gt hx) hr
  have hfun : complexCell k w =
      ((a+2:ℝ):ℂ)^z-2*((a+1:ℝ):ℂ)^z+(a:ℂ)^z := by
    simp only [complexCell, baseTwoComplexMaterialGradient, baseTwoCellRightEdge_eq,
      baseTwoCellLeftEdge_eq, a, z, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ofNat]
    push_cast
    ring
  rw [hfun]
  apply baseTwoSecondDifference_norm_le
    (fun x => (x:ℂ)^z) (fun x => z*(x:ℂ)^(z-1))
    (fun x => z*(z-1)*(x:ℂ)^(z-2)) a (2/a^2)
  · intro x hx; exact hder z x (ha.trans_le hx.1)
  · intro x hx
    simpa only [show z-1-1=z-2 by ring, mul_assoc] using
      (hder (z-1) x (ha.trans_le hx.1)).const_mul z
  · intro x hx
    have hx0 := ha.trans_le hx.1
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have hpow : x^((z-2).re) ≤ a^(-2:ℝ) := by
      apply (Real.rpow_le_rpow_of_exponent_le (ha1.trans hx.1) ?_).trans
        (Real.rpow_le_rpow_of_nonpos ha hx.1 (by norm_num))
      simp only [Complex.sub_re]; norm_num; linarith
    have h := mul_le_mul (mul_le_mul hz hz1 (norm_nonneg _) (by norm_num))
      hpow (Real.rpow_nonneg hx0.le _) (by norm_num : (0:ℝ) ≤ 1*2)
    simpa only [Real.rpow_neg (le_of_lt ha), Real.rpow_two, one_mul, div_eq_mul_inv] using h

/-- Complex normalized Taylor coefficient, only an analytic observation of
an already synthesized whole cell. -/
def complexJet (m : ℕ) (f : ℂ → ℂ) : ℂ := iteratedDeriv m f 0 / (m.factorial:ℂ)

theorem complex_jet_bound (m k : ℕ) :
    ‖complexJet m (complexCell k)‖ ≤ 2^(m+1) / ((4*k+3:ℕ):ℝ)^2 := by
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    (c:=(0:ℂ)) (f:=complexCell k) m (by norm_num : (0:ℝ) < 1/2)
    (complex_cell_entire k).diffContOnCl
    (by
      intro w hw
      apply complex_cell_bound k w
      have he : ‖w‖ = (1/2:ℝ) := by simpa only [Metric.mem_sphere, dist_zero_right] using hw
      exact he.le)
  rw [complexJet, norm_div, Complex.norm_natCast]
  apply (div_le_iff₀ (by positivity : (0:ℝ) < m.factorial)).2
  have hf : (m.factorial:ℝ) ≠ 0 := by positivity
  have ha : (((4*k+3:ℕ):ℝ)^2) ≠ 0 := by positivity
  have hr : ((1/2:ℝ)^m) = (2^m)⁻¹ := by rw [one_div, inv_pow]
  rw [hr, div_inv_eq_mul] at h
  have he : (2:ℝ)^(m+1) / ((4*k+3:ℕ):ℝ)^2 * m.factorial =
      m.factorial * (2 / ((4*k+3:ℕ):ℝ)^2) * 2^m := by rw [pow_succ]; ring
  rw [he]
  exact h

end
end CarryCellTail
