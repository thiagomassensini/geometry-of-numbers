import GeometryOfNumbers.Analysis.BaseTwoCompletedBoundaryDynamics
import GeometryOfNumbers.Analysis.IntegerIncidenceEnergy
import GeometryOfNumbers.Analysis.C2FiberRealDynamics

/-! Real coordinates of the EXISTING material source, not a freely selected
field. Its amplitude and phase are the prescribed historical initial-state
orbit. Finite point readouts recover it from the already completed Hilbert
source (seed, material gradient, derived return), without putting the raw
half-density sequence itself into l2. No new metric or dynamics is defined. -/
namespace GeometryOfNumbers.Analysis
open BaseTwoCompletion
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false

def carryMaterialRealSample (t : ℝ) (n : ℕ) : RealPlaneState :=
  ((criticalMaterialSample t n).re, (criticalMaterialSample t n).im)

theorem carryMaterialRealSample_coordinates (t : ℝ) (n : ℕ) :
    carryMaterialRealSample t n =
      ((Real.sqrt (n : ℝ))⁻¹ * Real.cos (-t * Real.log n),
        (Real.sqrt (n : ℝ))⁻¹ * Real.sin (-t * Real.log n)) := by
  apply Prod.ext <;>
    simp only [carryMaterialRealSample, criticalMaterialSample, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.neg_re, Complex.neg_im, Complex.exp_re, Complex.exp_im,
      mul_zero, zero_mul, mul_one, sub_zero, add_zero, neg_zero, Real.exp_zero,
      one_mul, Real.cos_neg, Real.sin_neg, neg_mul, mul_neg]

theorem carryMaterial_amplitude_depth_one (n : ℕ) (hn : 0 < n) :
    realCriticalAmplitude n 1 hn = (Real.sqrt (n : ℝ))⁻¹ := by
  rw [realCriticalAmplitude_eq_rpow, Real.sqrt_eq_rpow,
    ← Real.rpow_neg (Nat.cast_nonneg n)]
  norm_num

/-- The preexisting real depth state realizes exactly the prescribed point
sample. This matches amplitudes; it does not derive the phase law from depth. -/
theorem carryMaterialRealSample_eq_depthState (t : ℝ) (n : ℕ) (hn : 0 < n) :
    carryMaterialRealSample t n =
      realCriticalDepthState n 1 hn (-t * Real.log n) := by
  rw [carryMaterialRealSample_coordinates, realCriticalDepthState_eq_coordinates,
    carryMaterial_amplitude_depth_one]

/-- Product decomposition of the ORIGINAL point amplitude. The horizontal
factor is derived, not fitted to equalize two camera energies. -/
theorem carryMaterial_camera_amplitude_factorization (b k m : ℕ)
    (hb : 0 < b) (hm : 0 < m) :
    realCriticalAmplitude (b ^ k * m) 1 (by positivity) =
      realCriticalAmplitude b k hb * realCriticalAmplitude m 1 hm := by
  simp only [realCriticalAmplitude_eq_rpow, Nat.cast_one, neg_div, one_div,
    Nat.cast_mul, Nat.cast_pow]
  rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast_mul (by positivity)]
  congr 1
  ring_nf

theorem carryMaterialRealSample_camera_factorization (b k m : ℕ)
    (hb : 0 < b) (hm : 0 < m) (t : ℝ) :
    carryMaterialRealSample t (b ^ k * m) =
      scaleRealPlane (realCriticalAmplitude m 1 hm)
        (realCriticalDepthState b k hb (-t * Real.log (b ^ k * m : ℕ))) := by
  rw [carryMaterialRealSample_eq_depthState _ _ (by positivity),
    realCriticalDepthState_eq_coordinates, realCriticalDepthState_eq_coordinates,
    carryMaterial_camera_amplitude_factorization b k m hb hm]
  apply Prod.ext <;> simp only [scaleRealPlane] <;> ring

/-- The core is recovered from the original residual tower. Its positivity
follows from a positive quantity and exact reconstruction, not an extra input. -/
theorem carryMaterialTower_center_realization (b n k : ℕ) (hb : 0 < b)
    (hk : Geometry.HasCarryDepthAtLeast b n k) (hn : 0 < n) (t : ℝ) :
    let m := (Geometry.integerCameraTowerCell b n k).core
    ∃ hm : 0 < m, carryMaterialRealSample t n =
      scaleRealPlane (realCriticalAmplitude m 1 hm)
        (realCriticalDepthState b k hb (-t * Real.log n)) := by
  have hr := Geometry.integerCameraTowerCell_reconstruction b n k hb hk
  change b ^ k * (Geometry.integerCameraTowerCell b n k).core = n at hr
  have hm : 0 < (Geometry.integerCameraTowerCell b n k).core := by
    by_contra h
    have hz := Nat.eq_zero_of_not_pos h
    rw [hz, Nat.mul_zero] at hr
    omega
  refine ⟨hm, ?_⟩
  simpa only [hr] using (carryMaterialRealSample_camera_factorization
    b k (Geometry.integerCameraTowerCell b n k).core hb hm t)

/-- Finite coordinate evaluation on the EXISTING completed source carrier. -/
def carryMaterialGradientReadout (j : ℕ) : BaseTwoCompletedBoundaryHilbertCarrier →L[ℂ] ℂ :=
  (lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 j).comp
    ((WithLp.fstL 2 ℂ MaterialEdgeL2 ℂ).comp
      (WithLp.sndL 2 ℂ ℂ (WithLp 2 (MaterialEdgeL2 × ℂ))))

theorem carryMaterialGradientReadout_apply (j : ℕ) (y : BaseTwoCompletedBoundaryHilbertCarrier) :
    carryMaterialGradientReadout j y = y.snd.fst j := rfl

/-- Positive point n is reconstructed from seed and the first n-1 edges.
The total convention at zero is not a physical logarithmic point. -/
def carryMaterialPointReadout (n : ℕ) : BaseTwoCompletedBoundaryHilbertCarrier →L[ℂ] ℂ :=
  WithLp.fstL 2 ℂ ℂ (WithLp 2 (MaterialEdgeL2 × ℂ)) +
    ∑ j ∈ Finset.range (n - 1), carryMaterialGradientReadout j

theorem carryMaterialPointReadout_apply (n : ℕ) (y : BaseTwoCompletedBoundaryHilbertCarrier) :
    carryMaterialPointReadout n y = y.fst + ∑ j ∈ Finset.range (n - 1), y.snd.fst j := by
  simp [carryMaterialPointReadout, carryMaterialGradientReadout_apply]

theorem carryMaterialPointReadout_source (n : ℕ) (hn : 0 < n) (t : ℝ) :
    carryMaterialPointReadout n (baseTwoCompletedBoundaryHilbertState t) =
      criticalMaterialSample t n := by
  rw [carryMaterialPointReadout_apply]
  simp only [baseTwoCompletedBoundaryHilbertState_seed,
    baseTwoCompletedBoundaryHilbertState_interior,
    baseTwoCompletedMaterialGradientL2_apply, baseTwoCompletedMaterialGradient_apply]
  simpa only [Nat.sub_add_cancel (Nat.succ_le_of_lt hn)] using
    (criticalMaterialSample_eq_seed_add_gradientPrefix t (n - 1)).symm

theorem carryMaterialPointReadout_step (n : ℕ) (y : BaseTwoCompletedBoundaryHilbertCarrier) :
    carryMaterialPointReadout (n + 2) y - carryMaterialPointReadout (n + 1) y =
      y.snd.fst n := by
  simp only [carryMaterialPointReadout_apply, Nat.add_sub_cancel,
    show n + 2 - 1 = n + 1 by omega, Finset.sum_range_succ]
  abel

/-- Both cameras read one and the same existing completed source. -/
theorem carryMaterial72_common_center (t : ℝ) :
    scaleRealPlane (realCriticalAmplitude 9 1 (by decide))
        (realCriticalDepthState 2 3 (by decide) (-t * Real.log 72)) =
      carryMaterialRealSample t 72 ∧
    scaleRealPlane (realCriticalAmplitude 8 1 (by decide))
        (realCriticalDepthState 3 2 (by decide) (-t * Real.log 72)) =
      carryMaterialRealSample t 72 := by
  constructor
  · simpa using (carryMaterialRealSample_camera_factorization 2 3 9 (by decide) (by decide) t).symm
  · simpa using (carryMaterialRealSample_camera_factorization 3 2 8 (by decide) (by decide) t).symm

/-- The source pairing keeps the return coordinate as well as the interior.
No finite point readout is identified with this full carrier pairing. -/
theorem carryMaterial_completed_source_pairing (t u : ℝ) :
    inner ℂ (baseTwoCompletedBoundaryHilbertState t) (baseTwoCompletedBoundaryHilbertState u) =
      inner ℂ (criticalMaterialSample t 1) (criticalMaterialSample u 1) +
        (inner ℂ (baseTwoCompletedMaterialGradientL2 t) (baseTwoCompletedMaterialGradientL2 u) +
          inner ℂ (baseTwoCompletedBoundaryValue t) (baseTwoCompletedBoundaryValue u)) := rfl

end
end GeometryOfNumbers.Analysis
