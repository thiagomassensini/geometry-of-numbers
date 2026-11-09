import SigmaC5PiInterval
import ZetaLean.IntervalCExp
import Mathlib.Tactic

/-!
# Reuse the C5 certified `log π` interval for the C3 contour evaluator

The C5 module already proves a rational interval enclosure of `Real.log Real.pi`.
This bridge embeds that real interval into a complex rectangle containing the exact
`Complex.log (Real.pi : ℂ)` used by the radius-51 source response. No C5 table or
node evaluation is repeated here.
-/

namespace CarrySigmaObstruction

open ZetaLean

noncomputable section
set_option autoImplicit false

/-- Complex rectangle formed from the existing C5 interval for `log π`. -/
def contour51C5LogPiBox : ComplexInterval :=
  { re := c5PiLogInterval 160, im := Interval.exact 0 }

/-- The C5 real `log π` interval contains the exact complex logarithm of real π. -/
theorem contour51C5LogPiBox_contains :
    contour51C5LogPiBox.contains (Complex.log (Real.pi : ℂ)) := by
  rw [← Complex.ofReal_log Real.pi_pos.le]
  constructor
  · simpa [contour51C5LogPiBox, Complex.ofReal_re] using
      (c5_pi_log_interval_contains 160)
  · simp [contour51C5LogPiBox, Interval.contains, Interval.exact, Complex.ofReal_im]

#print axioms contour51C5LogPiBox_contains

end
end CarrySigmaObstruction
