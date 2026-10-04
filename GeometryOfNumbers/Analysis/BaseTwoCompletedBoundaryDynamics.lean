import GeometryOfNumbers.Analysis.BaseTwoCompletedBoundaryHilbert
import GeometryOfNumbers.Analysis.BaseTwoCompletedSignalRegularity

/-! # Component dynamics of the completed boundary realization

The interior is a material difference, not a raw material sample. Its induced
clock has a reconstruction term. These coordinate derivative laws do not
assert strong differentiability in ℓ² or define an autonomous Hilbert operator.
-/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators lp ENNReal
namespace GeometryOfNumbers.Analysis.BaseTwoCompletion

/-- The existing material sample has the material log-clock derivative. -/
theorem criticalMaterialSample_hasDerivAt (t : ℝ) (n : ℕ) :
    HasDerivAt (fun u => criticalMaterialSample u n)
      (-Complex.I * (Real.log (n : ℝ) : ℂ) * criticalMaterialSample t n) t := by
  have hc : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
  have he := (((hc.mul_const (Real.log (n : ℝ) : ℂ)).mul_const Complex.I).neg).cexp
  have hs := he.const_mul (((Real.sqrt (n : ℝ))⁻¹ : ℝ) : ℂ)
  convert hs using 1 <;> first
    | rfl
    | (funext u; simp only [criticalMaterialSample, Complex.ofReal_mul, Pi.neg_apply])
    | (simp only [criticalMaterialSample, Complex.ofReal_mul, Pi.neg_apply]; ring_nf)

/-- Exact coordinate derivative of the material-edge interior. -/
theorem criticalMaterialGradient_hasDerivAt (t : ℝ) (j : ℕ) :
    HasDerivAt (fun u => criticalMaterialGradient u j)
      (-Complex.I *
        ((Real.log ((j + 2 : ℕ) : ℝ) : ℂ) * criticalMaterialSample t (j + 2) -
          (Real.log ((j + 1 : ℕ) : ℝ) : ℂ) * criticalMaterialSample t (j + 1))) t := by
  convert (criticalMaterialSample_hasDerivAt t (j + 2)).sub
    (criticalMaterialSample_hasDerivAt t (j + 1)) using 1 <;>
    first | rfl | ring

/-- Residual when the old diagonal log(j+1) clock is applied to a material edge. -/
def baseTwoMaterialGradientDiagonalClockResidual (t : ℝ) (j : ℕ) : ℂ :=
  -Complex.I *
    ((Real.log ((j + 2 : ℕ) : ℝ) : ℂ) - (Real.log ((j + 1 : ℕ) : ℝ) : ℂ)) *
      criticalMaterialSample t (j + 2)

theorem criticalMaterialGradient_deriv_eq_diagonalClock_add_residual (t : ℝ) (j : ℕ) :
    deriv (fun u => criticalMaterialGradient u j) t =
      -Complex.I * (Real.log ((j + 1 : ℕ) : ℝ) : ℂ) * criticalMaterialGradient t j +
        baseTwoMaterialGradientDiagonalClockResidual t j := by
  rw [(criticalMaterialGradient_hasDerivAt t j).deriv]
  unfold criticalMaterialGradient baseTwoMaterialGradientDiagonalClockResidual
  ring

/-- The induced material clock coordinate uses finite reconstruction from
seed and preceding edges. It is defined independently of any moments. -/
def baseTwoCompletedBoundaryHilbertClockCoordinate
    (y : BaseTwoCompletedBoundaryHilbertCarrier) (j : ℕ) : ℂ :=
  (Real.log ((j + 2 : ℕ) : ℝ) : ℂ) * y.snd.fst j +
    ((Real.log ((j + 2 : ℕ) : ℝ) : ℂ) - (Real.log ((j + 1 : ℕ) : ℝ) : ℂ)) *
      (y.fst + ∑ k ∈ Finset.range j, y.snd.fst k)

/-- Finite reconstruction gives the correct clock coordinate on the completed state. -/
theorem baseTwoCompletedBoundaryHilbertClockCoordinate_eq (t : ℝ) (j : ℕ) :
    baseTwoCompletedBoundaryHilbertClockCoordinate
      (baseTwoCompletedBoundaryHilbertState t) j =
      (Real.log ((j + 2 : ℕ) : ℝ) : ℂ) * criticalMaterialSample t (j + 2) -
        (Real.log ((j + 1 : ℕ) : ℝ) : ℂ) * criticalMaterialSample t (j + 1) := by
  simp only [baseTwoCompletedBoundaryHilbertClockCoordinate,
    baseTwoCompletedBoundaryHilbertState_seed, baseTwoCompletedBoundaryHilbertState_interior,
    baseTwoCompletedMaterialGradientL2_apply, baseTwoCompletedMaterialGradient_apply]
  rw [← criticalMaterialSample_eq_seed_add_gradientPrefix]
  unfold criticalMaterialGradient
  ring

theorem baseTwoCompletedBoundaryHilbertInterior_coordinate_hasDerivAt (t : ℝ) (j : ℕ) :
    HasDerivAt (fun u => (baseTwoCompletedBoundaryHilbertState u).snd.fst j)
      (-Complex.I * baseTwoCompletedBoundaryHilbertClockCoordinate
        (baseTwoCompletedBoundaryHilbertState t) j) t := by
  simpa only [baseTwoCompletedBoundaryHilbertState_interior,
    baseTwoCompletedMaterialGradientL2_apply, baseTwoCompletedMaterialGradient_apply,
    baseTwoCompletedBoundaryHilbertClockCoordinate_eq] using
      criticalMaterialGradient_hasDerivAt t j

/-- The diagonal-clock residual is genuinely nonzero already at the first edge. -/
theorem baseTwoMaterialGradientDiagonalClockResidual_zeroEdge_ne_zero (t : ℝ) :
    baseTwoMaterialGradientDiagonalClockResidual t 0 ≠ 0 := by
  have hl : (Real.log 2 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hs : criticalMaterialSample t 2 ≠ 0 := by
    unfold criticalMaterialSample
    apply mul_ne_zero
    · exact Complex.ofReal_ne_zero.mpr (inv_ne_zero (Real.sqrt_ne_zero'.mpr (by norm_num)))
    · exact Complex.exp_ne_zero _
  simpa [baseTwoMaterialGradientDiagonalClockResidual] using
      mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
        (Complex.ofReal_ne_zero.mpr hl)) hs

/-- The simple diagonal log(j+1) action is not the interior evolution law. -/
theorem criticalMaterialGradient_deriv_zeroEdge_ne_diagonalClock (t : ℝ) :
    deriv (fun u => criticalMaterialGradient u 0) t ≠
      -Complex.I * (Real.log (1 : ℝ) : ℂ) * criticalMaterialGradient t 0 := by
  rw [criticalMaterialGradient_deriv_eq_diagonalClock_add_residual]
  simpa only [Nat.zero_add, Nat.cast_one, Real.log_one, Complex.ofReal_zero,
    mul_zero, zero_mul, zero_add] using
      baseTwoMaterialGradientDiagonalClockResidual_zeroEdge_ne_zero t

/-- The seed is constant under the material orbit. -/
theorem baseTwoCompletedBoundaryHilbertSeed_hasDerivAt (t : ℝ) :
    HasDerivAt (fun u => (baseTwoCompletedBoundaryHilbertState u).fst) 0 t := by
  simpa only [baseTwoCompletedBoundaryHilbertState_seed, criticalMaterialSample_one] using
    (hasDerivAt_const t (1 : ℂ))

/-- The boundary derivative is inherited from the already synthesized analytic
signal. This is a derivative theorem, not its primary boundary definition. -/
theorem baseTwoCompletedBoundaryValue_hasDerivAt (t : ℝ) :
    HasDerivAt baseTwoCompletedBoundaryValue (deriv baseTwoCriticalCompleteSignal t) t := by
  have he : baseTwoCompletedBoundaryValue = fun u => baseTwoCriticalCompleteSignal u - 1 := by
    funext u
    rw [baseTwoCompletedBoundaryValue_eq_readout_sub_seed,
      baseTwoCompletedUndressedReadout_eq_signal, criticalMaterialSample_one]
  rw [he]
  exact (baseTwoCriticalCompleteSignal_analyticAt t).differentiableAt.hasDerivAt.sub_const 1

end GeometryOfNumbers.Analysis.BaseTwoCompletion
