import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

/-!
Prime-power cameras are layers of the original prime's depth camera.
This lemma only concerns positive integers; padicValNat 2 0 is a special
convention and zero is outside the positive integer support here.

No Green, zeta, moment, or spectral property is involved.
-/
namespace CarryWheelNativeSignedGate

theorem all_dyadic_power_cameras_resolved_by_c2_depth
    (n k : ℕ) (hn : n ≠ 0) :
    2^k ∣ n ↔ k ≤ padicValNat 2 n :=
  padicValNat_dvd_iff_le (p := 2) hn

theorem camera_four_resolved_by_c2_depth
    (n : ℕ) (hn : n ≠ 0) :
    4 ∣ n ↔ 2 ≤ padicValNat 2 n := by
  simpa only [show (4 : ℕ) = 2^2 by norm_num] using
    (all_dyadic_power_cameras_resolved_by_c2_depth n 2 hn)

end CarryWheelNativeSignedGate
