import SigmaFiniteRationalIntervalSigns

/-!
# Conditional finite C2 Padé signs

The theorems below conclude signs for the original `sigmaPadeD` under explicit
source-coefficient box hypotheses. They do not prove those analytic hypotheses.
-/

namespace CarrySigmaObstruction

open CarrySigmaSource CarrySigmaPade

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000

theorem sigmaC00495CoefficientBall_valid :
    ∀ i ≤ 14, sigmaRatBallValid (sigmaC00495CoefficientBall i) := by
  intro i hi
  interval_cases i <;>
    norm_num [sigmaRatBallValid, sigmaC00495CoefficientBall]

theorem sigmaC01CoefficientBall_valid :
    ∀ i ≤ 12, sigmaRatBallValid (sigmaC01CoefficientBall i) := by
  intro i hi
  interval_cases i <;>
    norm_num [sigmaRatBallValid, sigmaC01CoefficientBall]

theorem sigmaC00495_scaled_moment_boxes
    (hboxes : sigmaC00495SourceBoxes) :
    ∀ n, n + 1 ≤ 14 →
      sigmaRatBallContains
        (sigmaFiniteScaledMomentBall sigmaC00495CoefficientBall n)
        (completedSigmaFiniteScaledMoment (99 / 2000) n) := by
  apply sigmaFiniteScaledMomentBall_contains_of_recurrence
    sigmaC00495CoefficientBall
    (completedSigmaDisplacedSourceCoefficient (99 / 2000))
    (completedSigmaFiniteScaledMoment (99 / 2000)) 14
  · exact sigmaC00495CoefficientBall_valid
  · intro i hi
    exact hboxes i (by omega)
  · intro n hn
    exact completedSigmaFiniteScaledMoment_recurrence (99 / 2000)
      (by norm_num) (by norm_num) n

theorem sigmaC01_scaled_moment_boxes
    (hboxes : sigmaC01SourceBoxes) :
    ∀ n, n + 1 ≤ 12 →
      sigmaRatBallContains
        (sigmaFiniteScaledMomentBall sigmaC01CoefficientBall n)
        (completedSigmaFiniteScaledMoment (1 / 10) n) := by
  apply sigmaFiniteScaledMomentBall_contains_of_recurrence
    sigmaC01CoefficientBall
    (completedSigmaDisplacedSourceCoefficient (1 / 10))
    (completedSigmaFiniteScaledMoment (1 / 10)) 12
  · exact sigmaC01CoefficientBall_valid
  · intro i hi
    exact hboxes i (by omega)
  · intro n hn
    exact completedSigmaFiniteScaledMoment_recurrence (1 / 10)
      (by norm_num) (by norm_num) n

theorem sigmaPadeD_signs_at_99_2000_of_source_boxes
    (hboxes : sigmaC00495SourceBoxes) :
    (∀ s < 11, 0 < sigmaPadeD (99 / 2000) s) ∧
      sigmaPadeD (99 / 2000) 11 < 0 := by
  have hmoment := sigmaC00495_scaled_moment_boxes hboxes
  have hvalid := sigmaC00495CoefficientBall_valid
  constructor
  · intro s hs
    have hminor := sigmaFiniteScaledMomentBallMinor_contains
      sigmaC00495CoefficientBall
      (completedSigmaFiniteScaledMoment (99 / 2000)) 14 s (by omega)
      hvalid (hmoment s (by omega)) (hmoment (s + 1) (by omega))
      (hmoment (s + 2) (by omega))
    have hminorPos := sigmaRatBallContains_pos_of_lower
      (sigmaC00495Minor_lower_pos s hs) hminor
    exact sigmaPadeD_pos_of_completedSigmaFiniteScaledMoment_minor_pos
      (99 / 2000) (by norm_num) (by norm_num) s hminorPos
  · have hminor := sigmaFiniteScaledMomentBallMinor_contains
      sigmaC00495CoefficientBall
      (completedSigmaFiniteScaledMoment (99 / 2000)) 14 11 (by omega)
      hvalid (hmoment 11 (by omega)) (hmoment 12 (by omega))
      (hmoment 13 (by omega))
    have hminorNeg := sigmaRatBallContains_neg_of_upper
      sigmaC00495Minor_final_neg hminor
    exact sigmaPadeD_neg_of_completedSigmaFiniteScaledMoment_minor_neg
      (99 / 2000) (by norm_num) (by norm_num) 11 hminorNeg

theorem sigmaPadeD_signs_at_1_10_of_source_boxes
    (hboxes : sigmaC01SourceBoxes) :
    (∀ s < 9, 0 < sigmaPadeD (1 / 10) s) ∧
      sigmaPadeD (1 / 10) 9 < 0 := by
  have hmoment := sigmaC01_scaled_moment_boxes hboxes
  have hvalid := sigmaC01CoefficientBall_valid
  constructor
  · intro s hs
    have hminor := sigmaFiniteScaledMomentBallMinor_contains
      sigmaC01CoefficientBall
      (completedSigmaFiniteScaledMoment (1 / 10)) 12 s (by omega)
      hvalid (hmoment s (by omega)) (hmoment (s + 1) (by omega))
      (hmoment (s + 2) (by omega))
    have hminorPos := sigmaRatBallContains_pos_of_lower
      (sigmaC01Minor_lower_pos s hs) hminor
    exact sigmaPadeD_pos_of_completedSigmaFiniteScaledMoment_minor_pos
      (1 / 10) (by norm_num) (by norm_num) s hminorPos
  · have hminor := sigmaFiniteScaledMomentBallMinor_contains
      sigmaC01CoefficientBall (completedSigmaFiniteScaledMoment (1 / 10)) 12 9 (by omega)
      hvalid (hmoment 9 (by omega)) (hmoment 10 (by omega))
      (hmoment 11 (by omega))
    have hminorNeg := sigmaRatBallContains_neg_of_upper
      sigmaC01Minor_final_neg hminor
    exact sigmaPadeD_neg_of_completedSigmaFiniteScaledMoment_minor_neg
      (1 / 10) (by norm_num) (by norm_num) 9 hminorNeg

end
end CarrySigmaObstruction

#print axioms CarrySigmaObstruction.sigmaC00495_scaled_moment_boxes
#print axioms CarrySigmaObstruction.sigmaC01_scaled_moment_boxes
#print axioms CarrySigmaObstruction.sigmaPadeD_signs_at_99_2000_of_source_boxes
#print axioms CarrySigmaObstruction.sigmaPadeD_signs_at_1_10_of_source_boxes
