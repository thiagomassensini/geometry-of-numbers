import SigmaPadeCorrespondence
import SigmaCentralTenModeRationalGate

/-!
# Conditional positivity theorem for the original central C2 minors

This theorem keeps the original `completedSigmaLogJet` and `sigmaPadeD` as the source.  The
ten-mode expansion and weighted-tail bounds remain explicit hypotheses until the analytic bridge
from the original continuation has been formalized.
-/

namespace CarrySigmaPade

theorem sigmaPadeD_center_pos_of_conditional_ten_mode_tail
    (a : Fin 10 → ℝ) (e : ℕ → ℝ)
    (hdecomp : ∀ n,
      CarrySigmaSource.completedSigmaLogJet 0 n =
        CarrySigmaCentral.tenModeMoment a n + e n)
    (hbox : ∀ i,
      CarrySigmaCentral.scaleLower i ≤ a i ∧ a i ≤ CarrySigmaCentral.scaleUpper i)
    (he : ∀ n, |e n| ≤ 60 * CarrySigmaCentral.eta ^ (n + 1))
    (hnonneg : ∀ n, n ≤ 5 → 0 ≤ e n)
    (htail : ∀ n, 1 ≤ n → n ≤ 4 → e n ≤ CarrySigmaCentral.refinedTail n) :
    ∀ s, 0 < sigmaPadeD 0 s := by
  intro s
  have h := CarrySigmaCentral.central_hankel2_pos_of_ten_boxes_and_tail
    (H := fun n => CarrySigmaSource.completedSigmaLogJet 0 n) e a
    hdecomp hbox he hnonneg htail s
  simpa only [sigmaPadeD, CarrySigmaCentral.hankel2] using h

end CarrySigmaPade
