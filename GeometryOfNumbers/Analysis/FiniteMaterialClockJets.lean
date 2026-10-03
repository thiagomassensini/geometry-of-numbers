import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import GeometryOfNumbers.Analysis.FiniteNativeMaterialClock
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! Exact finite clock jets, before the historical scalar completion.
The coordinate j : Fin M represents the positive material integer j+1.
No assertion about the completed historical source is made here. -/

noncomputable section
open scoped BigOperators
namespace GeometryOfNumbers.Analysis.FiniteClockJets
open GeometryOfNumbers.Analysis.NativeMaterialClock

abbrev finiteMaterialClock (M : ℕ) := finiteRealSpectralGenerator M
abbrev finiteMaterialOrbit (M : ℕ) (t : ℝ) := finiteRealSpectralEvolution M t

def finiteMaterialBasis {M : ℕ} (j : Fin M) : FiniteRealSpectralHilbert M :=
  WithLp.toLp 2 (Pi.single j 1)

theorem finiteMaterialClock_basis {M : ℕ} (j : Fin M) :
    finiteMaterialClock M (finiteMaterialBasis j) =
      (Real.log ((j.val+1 : ℕ) : ℝ) : ℂ) • finiteMaterialBasis j := by
  ext k
  by_cases hk : k = j
  · subst k; simp [finiteMaterialBasis, finiteRealSpectralFrequency]
  · simp [finiteMaterialBasis, hk]

theorem finiteMaterialOrbit_basis {M : ℕ} (t : ℝ) (j : Fin M) :
    finiteMaterialOrbit M t (finiteMaterialBasis j) =
      finiteRealSpectralPhase t j • finiteMaterialBasis j := by
  ext k
  by_cases hk : k = j
  · subst k; simp [finiteMaterialBasis]
  · simp [finiteMaterialBasis, hk]

def clockRate {M : ℕ} (j : Fin M) : ℂ :=
  -Complex.I * (finiteRealSpectralFrequency j : ℂ)

theorem finitePhase_eq_exp {M : ℕ} (t : ℝ) (j : Fin M) :
    finiteRealSpectralPhase t j = Complex.exp (clockRate j * (t : ℂ)) := by
  unfold finiteRealSpectralPhase clockRate
  congr 1
  push_cast
  ring

private theorem exp_linear_hasDerivAt (a b : ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (a * (t : ℂ)) * b)
      (a * (Complex.exp (a * (t : ℂ)) * b)) t := by
  have h := ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul a).cexp.mul_const b
  simpa [Complex.ofRealCLM_apply, mul_comm, mul_left_comm, mul_assoc] using h

def clockJetOrbit {M : ℕ} (r : ℕ) (f : FiniteRealSpectralHilbert M)
    (t : ℝ) : FiniteRealSpectralHilbert M :=
  WithLp.toLp 2 (fun j => clockRate j ^ r * (finiteRealSpectralPhase t j * f j))

private theorem clockJetOrbit_hasDerivAt {M : ℕ} (r : ℕ)
    (f : FiniteRealSpectralHilbert M) (t : ℝ) :
    HasDerivAt (clockJetOrbit r f) (clockJetOrbit (r+1) f t) t := by
  have hpi : HasDerivAt
      (fun t : ℝ => fun j : Fin M => clockRate j ^ r * (finiteRealSpectralPhase t j * f j))
      (fun j : Fin M => clockRate j ^ (r+1) * (finiteRealSpectralPhase t j * f j)) t := by
    apply hasDerivAt_pi.mpr
    intro j
    have h := (exp_linear_hasDerivAt (clockRate j) (f j) t).const_mul (clockRate j ^ r)
    simpa only [finitePhase_eq_exp, pow_succ, mul_assoc] using h
  exact (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 _).comp_hasDerivAt t hpi

theorem finiteMaterialClockJet_all_times {M : ℕ} (r : ℕ)
    (f : FiniteRealSpectralHilbert M) :
    iteratedDeriv r (fun t : ℝ => finiteMaterialOrbit M t f) = clockJetOrbit r f := by
  induction r with
  | zero =>
      funext t
      ext j
      simp [clockJetOrbit]
  | succ r ih =>
      rw [iteratedDeriv_succ, ih]
      exact funext (fun t => (clockJetOrbit_hasDerivAt r f t).deriv)

def finiteClockStrongGenerator (M : ℕ) :
    Module.End ℂ (FiniteRealSpectralHilbert M) := -Complex.I • finiteMaterialClock M

theorem finiteClockStrongGenerator_pow_apply {M : ℕ} (r : ℕ)
    (f : FiniteRealSpectralHilbert M) (j : Fin M) :
    (finiteClockStrongGenerator M ^ r) f j = clockRate j ^ r * f j := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [pow_succ']
      change (-Complex.I) * ((finiteRealSpectralFrequency j : ℂ) *
        ((finiteClockStrongGenerator M ^ r) f j)) = _
      rw [ih, pow_succ]
      simp only [clockRate]
      ring

/-- The actual iterated strong derivative equals the power of -i L_M. -/
theorem finiteMaterialClockJet_eq_generatorPow {M : ℕ} (r : ℕ)
    (f : FiniteRealSpectralHilbert M) :
    iteratedDeriv r (fun t : ℝ => finiteMaterialOrbit M t f) 0 =
      (finiteClockStrongGenerator M ^ r) f := by
  rw [finiteMaterialClockJet_all_times]
  ext j
  simp [clockJetOrbit, finiteClockStrongGenerator_pow_apply]

theorem finiteMaterialClockJet_basis {M : ℕ} (r : ℕ) (j : Fin M) :
    iteratedDeriv r (fun t : ℝ => finiteMaterialOrbit M t (finiteMaterialBasis j)) 0 =
      clockRate j ^ r • finiteMaterialBasis j := by
  rw [finiteMaterialClockJet_eq_generatorPow]
  ext k
  by_cases hk : k = j
  · subst k; simp [finiteClockStrongGenerator_pow_apply, finiteMaterialBasis]
  · simp [finiteClockStrongGenerator_pow_apply, finiteMaterialBasis, hk]

/-- The pair used literally by quarter(k) in both recovered Python scripts. -/
def historicalQuarter (r : ℕ) : ℂ :=
  if r % 4 = 0 then 1 else if r % 4 = 1 then Complex.I
  else if r % 4 = 2 then -1 else -Complex.I

theorem historicalQuarter_eq_I_pow (r : ℕ) : historicalQuarter r = Complex.I ^ r := by
  rw [Complex.I_pow_eq_pow_mod]
  have h := Nat.mod_lt r (by omega : 0 < 4)
  interval_cases hr : r % 4 <;> simp [historicalQuarter, hr, Complex.I_sq, Complex.I_pow_three]

def historicalRotationCoefficient (amplitude angularRate : ℝ) (r : ℕ) : ℂ :=
  historicalQuarter r * ((amplitude * angularRate ^ r / r.factorial : ℝ) : ℂ)

theorem historicalRotationCoefficient_exact (amplitude angularRate : ℝ) (r : ℕ) :
    historicalRotationCoefficient amplitude angularRate r =
      (Complex.I * (angularRate : ℂ)) ^ r * (amplitude : ℂ) / (r.factorial : ℂ) := by
  simp only [historicalRotationCoefficient, historicalQuarter_eq_I_pow,
    Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_natCast, mul_pow]
  ring

def historicalInitialState (M : ℕ) : FiniteRealSpectralHilbert M :=
  WithLp.toLp 2 (fun j => ((Real.sqrt ((j.val+1 : ℕ) : ℝ))⁻¹ : ℝ))

def normalizedClockJet {M : ℕ} (r : ℕ) (f : FiniteRealSpectralHilbert M) :
    FiniteRealSpectralHilbert M :=
  ((r.factorial : ℂ)⁻¹) • (finiteClockStrongGenerator M ^ r) f

/-- Exact native_state_series coefficient, with both quadratures and factorial. -/
theorem nativeStateSeries_eq_normalizedClockJet {M : ℕ} (r : ℕ) (j : Fin M) :
    historicalRotationCoefficient ((Real.sqrt ((j.val+1 : ℕ) : ℝ))⁻¹)
      (-Real.log ((j.val+1 : ℕ) : ℝ)) r =
      normalizedClockJet r (historicalInitialState M) j := by
  rw [historicalRotationCoefficient_exact]
  simp only [normalizedClockJet, PiLp.smul_apply, smul_eq_mul,
    finiteClockStrongGenerator_pow_apply, historicalInitialState,
    clockRate, finiteRealSpectralFrequency, Complex.ofReal_neg]
  ring

/-- Real/imaginary pairs in Python correspond to these exact two quadratures. -/
theorem nativeStateSeries_quadratures {M : ℕ} (r : ℕ) (j : Fin M) :
    ((historicalRotationCoefficient ((Real.sqrt ((j.val+1 : ℕ) : ℝ))⁻¹)
      (-Real.log ((j.val+1 : ℕ) : ℝ)) r).re,
     (historicalRotationCoefficient ((Real.sqrt ((j.val+1 : ℕ) : ℝ))⁻¹)
      (-Real.log ((j.val+1 : ℕ) : ℝ)) r).im) =
    ((normalizedClockJet r (historicalInitialState M) j).re,
     (normalizedClockJet r (historicalInitialState M) j).im) := by
  rw [nativeStateSeries_eq_normalizedClockJet]

def finiteHeadReadout {M : ℕ} (weights : Fin M → ℝ) :
    FiniteRealSpectralHilbert M →ₗ[ℂ] ℂ where
  toFun f := ∑ j, (weights j : ℂ) * f j
  map_add' f g := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' a f := by simp [Finset.mul_sum, mul_left_comm]

def historicalFiniteHeadCoefficient {M : ℕ} (weights : Fin M → ℝ) (r : ℕ) : ℂ :=
  ∑ j, (weights j : ℂ) * historicalRotationCoefficient
    ((Real.sqrt ((j.val+1 : ℕ) : ℝ))⁻¹) (-Real.log ((j.val+1 : ℕ) : ℝ)) r

def historicalCameraPeriod (camera : ℕ) : ℕ := if camera = 2 then 4 else camera
def historicalCameraRadiiCount (camera : ℕ) : ℕ := if camera = 2 then 1 else camera / 2
def historicalHeadDimension (camera cutoff : ℕ) : ℕ :=
  historicalCameraPeriod camera * cutoff + historicalCameraRadiiCount camera

/-- Literal finite_weight_map: signed brackets, scalarized before completion. -/
def historicalCameraWeight (camera cutoff n : ℕ) : ℝ :=
  (if 1 ≤ n ∧ n ≤ historicalCameraRadiiCount camera then 1 else 0) +
    ∑ k ∈ Finset.range cutoff,
      ((if n = historicalCameraPeriod camera * (k+1)
        then -2 * (historicalCameraRadiiCount camera : ℝ) else 0) +
      ∑ a ∈ Finset.range (historicalCameraRadiiCount camera),
        ((if n = historicalCameraPeriod camera * (k+1) - (a+1) then 1 else 0) +
        (if n = historicalCameraPeriod camera * (k+1) + (a+1) then 1 else 0)))

def historicalCameraWeights (camera cutoff : ℕ) :
    Fin (historicalHeadDimension camera cutoff) → ℝ :=
  fun j => historicalCameraWeight camera cutoff (j.val+1)

/-- Exact canary for the production defaults CAMERA=2, CUTOFF=2: M=9. -/
theorem historicalCameraWeights_default :
    historicalCameraWeights 2 2 = ![1,0,1,-2,1,0,1,-2,1] := by
  funext j
  fin_cases j <;>
    norm_num [historicalCameraWeights, historicalCameraWeight,
      historicalCameraPeriod, historicalCameraRadiiCount, historicalHeadDimension,
      Finset.sum_range_succ, Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> rfl

/-- This certifies the historical HEAD, before independent tail/dressing data. -/
theorem finiteClockJets_to_head {M : ℕ} (weights : Fin M → ℝ) (r : ℕ) :
    historicalFiniteHeadCoefficient weights r =
      finiteHeadReadout weights (normalizedClockJet r (historicalInitialState M)) := by
  simp only [historicalFiniteHeadCoefficient, nativeStateSeries_eq_normalizedClockJet,
    finiteHeadReadout, LinearMap.coe_mk, AddHom.coe_mk]

theorem finiteHeadReadout_iteratedDerivative {M : ℕ} (weights : Fin M → ℝ)
    (f : FiniteRealSpectralHilbert M) (r : ℕ) :
    iteratedDeriv r (fun t : ℝ => finiteHeadReadout weights (finiteMaterialOrbit M t f)) 0 =
      finiteHeadReadout weights ((finiteClockStrongGenerator M ^ r) f) := by
  let R := (finiteHeadReadout weights).toContinuousLinearMap
  have h : ∀ k, iteratedDeriv k (fun t : ℝ => R (finiteMaterialOrbit M t f)) =
      (fun t : ℝ => R (clockJetOrbit k f t)) := by
    intro k
    induction k with
    | zero =>
        funext t
        have he : finiteMaterialOrbit M t f = clockJetOrbit 0 f t := by
          ext j
          simp [clockJetOrbit]
        exact congrArg R he
    | succ k ih =>
        rw [iteratedDeriv_succ, ih]
        funext t
        exact (((R.restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt t
          (clockJetOrbit_hasDerivAt k f t)).deriv
  change iteratedDeriv r (fun t : ℝ => R (finiteMaterialOrbit M t f)) 0 = _
  rw [h]
  change finiteHeadReadout weights (clockJetOrbit r f 0) = _
  rw [← finiteMaterialClockJet_all_times, finiteMaterialClockJet_eq_generatorPow]

/-- Each coordinate orbit is recovered globally from its entire Taylor tower. -/
theorem finiteMaterialOrbit_coordinate_hasSum {M : ℕ}
    (f : FiniteRealSpectralHilbert M) (t : ℝ) (j : Fin M) :
    HasSum (fun r : ℕ => normalizedClockJet r f j * (t : ℂ)^r)
      (finiteMaterialOrbit M t f j) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp (clockRate j * (t : ℂ))).mul_right (f j)
  rw [← Complex.exp_eq_exp_ℂ] at h
  have he : (fun r : ℕ => normalizedClockJet r f j * (t : ℂ)^r) =
      (fun r : ℕ => (clockRate j * (t : ℂ)) ^ r / (r.factorial : ℂ) * f j) := by
    funext r
    simp only [normalizedClockJet, PiLp.smul_apply, smul_eq_mul,
      finiteClockStrongGenerator_pow_apply, mul_pow]
    ring
  rw [he]
  simpa only [finiteRealSpectralEvolution_apply, finitePhase_eq_exp] using h

/-- Temporal scan of the finite head is exactly replaced by its Taylor tower. -/
theorem finiteHeadReadout_hasSum (M : ℕ) (weights : Fin M → ℝ) (t : ℝ) :
    HasSum (fun r : ℕ => historicalFiniteHeadCoefficient weights r * (t : ℂ)^r)
      (finiteHeadReadout weights (finiteMaterialOrbit M t (historicalInitialState M))) := by
  have h := hasSum_sum (s := Finset.univ) (fun j (_ : j ∈ (Finset.univ : Finset (Fin M))) =>
    (finiteMaterialOrbit_coordinate_hasSum (historicalInitialState M) t j).mul_left (weights j : ℂ))
  simpa [finiteClockJets_to_head, finiteHeadReadout, Finset.sum_mul, mul_assoc] using h

end GeometryOfNumbers.Analysis.FiniteClockJets
