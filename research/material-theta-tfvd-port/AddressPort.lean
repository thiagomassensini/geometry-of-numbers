import CarrySelfAdjointOperator.CompletedNativeXiCosineTransform
import CPFormal.Analytic.CpCarryAmplitudeIdentification
import NativeCarrySpectralWeyl.Boundary.GreenRelation
import Mathlib.Tactic

/-! An address-resolved lift of the ORIGINAL theta modes. Value, material
logarithm and theta-coordinate derivative are distinct channels. This record
of channels is not a new physical metric or a moment-defined Hilbert space. -/
namespace CarryMaterialTheta
open CarrySelfAdjointOperator XiThetaCosine CPFormal.Analytic.Cp
noncomputable section
set_option autoImplicit false

def addressMode (n : ℕ) (u : ℝ) : ℝ :=
  Real.exp (u/2) * Real.exp (-Real.pi * (n : ℝ)^2 * Real.exp (2*u))

def addressModeFirst (n : ℕ) (u : ℝ) : ℝ :=
  (1/2 - 2*Real.pi*(n : ℝ)^2*Real.exp (2*u)) * addressMode n u

theorem addressMode_succ (n : ℕ) : addressMode (n+1) = thetaTailMode n := rfl
theorem addressModeFirst_succ (n : ℕ) : addressModeFirst (n+1) = thetaTailModeFirst n := rfl

theorem addressMode_pos (n : ℕ) (u : ℝ) : 0 < addressMode n u := by
  unfold addressMode
  positivity

theorem addressMode_hasDerivAt {n : ℕ} (hn : 0 < n) (u : ℝ) :
    HasDerivAt (addressMode n) (addressModeFirst n u) u := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  exact hasDerivAt_thetaTailMode k u

theorem carry_amplitude_eq_exp {b : ℕ} (hb : 0 < b) :
    primeCarryAmplitudeRatio b = Real.exp (-(Real.log (b : ℝ))/2) := by
  rw [primeCarryAmplitudeRatio, Real.sqrt_eq_rpow,
    Real.rpow_def_of_pos (by exact_mod_cast hb), ← Real.exp_neg]
  congr 1
  ring

theorem exp_double_shift {b : ℕ} (hb : 0 < b) (u : ℝ) :
    Real.exp (2*(u+Real.log (b : ℝ))) = (b : ℝ)^2 * Real.exp (2*u) := by
  have h : 0 < (b : ℝ) := by exact_mod_cast hb
  rw [show 2*(u+Real.log (b : ℝ)) = Real.log (b : ℝ)+Real.log (b : ℝ)+2*u by ring,
    Real.exp_add, Real.exp_add, Real.exp_log h]
  ring

/-- Address dilation becomes translation in u with the ALREADY fixed Carry
amplitude. No primality, moment sequence or positivity premise enters. -/
theorem addressMode_dilation {b : ℕ} (hb : 0 < b) (n : ℕ) (u : ℝ) :
    addressMode (b*n) u =
      primeCarryAmplitudeRatio b * addressMode n (u+Real.log (b : ℝ)) := by
  have ha : primeCarryAmplitudeRatio b * Real.exp ((u+Real.log (b : ℝ))/2) =
      Real.exp (u/2) := by
    rw [carry_amplitude_eq_exp hb, ← Real.exp_add]
    congr 1
    ring
  simp only [addressMode, Nat.cast_mul]
  rw [exp_double_shift hb]
  rw [← mul_assoc, ha]
  congr 2
  ring

theorem addressModeFirst_dilation {b : ℕ} (hb : 0 < b) (n : ℕ) (u : ℝ) :
    addressModeFirst (b*n) u =
      primeCarryAmplitudeRatio b * addressModeFirst n (u+Real.log (b : ℝ)) := by
  simp only [addressModeFirst, Nat.cast_mul]
  rw [addressMode_dilation hb, exp_double_shift hb]
  ring

/-- Coordinates: value, then (material-log channel, theta derivative).
Complex coefficients keep both original real quadratures. -/
abbrev MaterialThetaPort := ℂ × (ℂ × ℂ)

def materialThetaMode (n : ℕ) (a : ℂ) (u : ℝ) : MaterialThetaPort :=
  (a * (addressMode n u : ℂ),
    (a * ((Real.log (n : ℝ) * addressMode n u : ℝ) : ℂ),
      a * (addressModeFirst n u : ℂ)))

/-- The native log channel acquires a real triangular shear, while the
theta derivative is translated without that shear. -/
def dilationShear (b : ℕ) (p : MaterialThetaPort) : MaterialThetaPort :=
  (p.1, (p.2.1 + (Real.log (b : ℝ) : ℂ)*p.1, p.2.2))

theorem materialThetaMode_dilation {b n : ℕ} (hb : 0 < b) (hn : 0 < n)
    (a : ℂ) (u : ℝ) :
    materialThetaMode (b*n) a u =
      (primeCarryAmplitudeRatio b : ℂ) •
        dilationShear b (materialThetaMode n a (u+Real.log (b : ℝ))) := by
  have hlog : Real.log ((b*n : ℕ) : ℝ) = Real.log (b : ℝ)+Real.log (n : ℝ) := by
    rw [Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
  simp only [materialThetaMode, dilationShear, Prod.smul_mk, smul_eq_mul,
    addressMode_dilation hb, addressModeFirst_dilation hb, hlog,
    Complex.ofReal_mul, Complex.ofReal_add]
  ext <;> ring

/-- Even at a fixed address, the full lift retains its complex coefficient. -/
theorem materialThetaMode_injective (n : ℕ) (u : ℝ) :
    Function.Injective (fun a : ℂ => materialThetaMode n a u) := by
  intro a d h
  have hv := congrArg Prod.fst h
  change a * (addressMode n u : ℂ) = d * (addressMode n u : ℂ) at hv
  exact mul_right_cancel₀ (Complex.ofReal_ne_zero.mpr (addressMode_pos n u).ne') hv

end
end CarryMaterialTheta
