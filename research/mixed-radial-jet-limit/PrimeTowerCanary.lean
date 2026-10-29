import OddSourceBoxes
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Audit of the two closed forms in the USER'S AUXILIARY prime-tower note.
No new physical source, moment sequence, Gram or metric is constructed here.
The all-order positive-series assertion is not needed for this obstruction. -/
namespace CarryMixedRadial
open CarrySelfAdjointOperator CarrySixthOdd CarrySixthEven CarryIntegralCertificate CarryCriticalSource
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536

/-- Reuse precisely the existing source enclosures, rather than numerical h's.
The same inequality appears in PR36; no clock or clock realization is imported. -/
theorem native_two_lt_one_sixteenth :
    canonicalCompletedNativeLogDerivativeMoment 2 <
      canonicalCompletedNativeLogDerivativeMoment 1 / 16 := by
  have h1 := mem_compactMomentBox 1
  have h2 := mem_compactMomentBox 2
  norm_num [compactMomentBox,compactMomentTable,Box.Mem,intervalScale] at h1 h2
  linarith

/-- The unscaled logarithmic support in the proposed closed forms imposes a
low-order gap, independently of the choice of decay parameter. -/
theorem tower_closed_forms_gap {a q : ℝ} (ha : 1/2 ≤ a) (hq : 0 < q) (hq1 : q < 1) :
    (1/2)*(a^2*q/(1-q)^2) ≤ a^3*q*(1+q)/(1-q)^3 := by
  have hd : 0 < 1-q := by linarith
  have ht : 0 < a^2*q/(1-q)^2 := by positivity
  have hr : 1 ≤ (1+q)/(1-q) := (le_div_iff₀ hd).mpr (by linarith)
  have he : a^3*q*(1+q)/(1-q)^3 =
      a*(a^2*q/(1-q)^2)*((1+q)/(1-q)) := by
    field_simp
  rw [he]
  calc
    _ ≤ a*(a^2*q/(1-q)^2) := mul_le_mul_of_nonneg_right ha ht.le
    _ ≤ _ := le_mul_of_one_le_right (by positivity) hr

/-- A global positive mass cannot fix the mismatch. This is a no-go for the
literal note formulas, not for completion/TFVD transports of the original source. -/
theorem tower_closed_forms_not_native {a q mass : ℝ}
    (ha : 1/2 ≤ a) (hq : 0 < q) (hq1 : q < 1) (hmass : 0 < mass) :
    ¬ (canonicalCompletedNativeLogDerivativeMoment 1 = mass*(a^2*q/(1-q)^2) ∧
       canonicalCompletedNativeLogDerivativeMoment 2 = mass*(a^3*q*(1+q)/(1-q)^3)) := by
  rintro ⟨h1,h2⟩
  have hgap := mul_le_mul_of_nonneg_left (tower_closed_forms_gap ha hq hq1) hmass.le
  have hp : 0 < mass*(a^2*q/(1-q)^2) := by
    have hd : 0 < 1-q := by linarith
    positivity
  have hn := native_two_lt_one_sixteenth
  rw [h1,h2] at hn
  nlinarith

theorem prime_log_ge_half {p : ℕ} (hp : Nat.Prime p) : (1/2 : ℝ) ≤ Real.log p := by
  have he : Real.log (2 : ℝ) ≤ Real.log (p : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hp.two_le)
  linarith [Real.log_two_gt_d9]

theorem prime_tower_closed_forms_not_native {p : ℕ} (hp : Nat.Prime p)
    {q mass : ℝ} (hq : 0 < q) (hq1 : q < 1) (hmass : 0 < mass) :
    ¬ (canonicalCompletedNativeLogDerivativeMoment 1 = mass*((Real.log p)^2*q/(1-q)^2) ∧
       canonicalCompletedNativeLogDerivativeMoment 2 = mass*((Real.log p)^3*q*(1+q)/(1-q)^3)) :=
  tower_closed_forms_not_native (prime_log_ge_half hp) hq hq1 hmass

end
end CarryMixedRadial
