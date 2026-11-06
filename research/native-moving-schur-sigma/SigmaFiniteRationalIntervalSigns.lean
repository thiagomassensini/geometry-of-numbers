import SigmaFiniteRationalIntervalTransport

/-!
# Kernel-checked signs for the C5 rational minor enclosures

These are statements about the exact rational interval calculation only. The
source coefficient inclusion hypotheses are not supplied in this file.
-/

namespace CarrySigmaObstruction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

theorem sigmaC00495Minor_lower_pos :
    ∀ s < 11, 0 < sigmaRatBallLower
      (sigmaFiniteScaledMomentBallMinor sigmaC00495CoefficientBall s) := by
  intro s hs
  interval_cases s <;>
    norm_num [sigmaRatBallLower, sigmaFiniteScaledMomentBallMinor,
      sigmaRatBallSub, sigmaFiniteScaledMomentBall, sigmaRatBallMul,
      sigmaRatBallNeg, sigmaRatBallPow, sigmaRatBallConst,
      sigmaC00495CoefficientBall, Finset.sum_range_succ]

theorem sigmaC00495Minor_final_neg :
    sigmaRatBallUpper
      (sigmaFiniteScaledMomentBallMinor sigmaC00495CoefficientBall 11) < 0 := by
  norm_num [sigmaRatBallUpper, sigmaFiniteScaledMomentBallMinor,
    sigmaRatBallSub, sigmaFiniteScaledMomentBall, sigmaRatBallMul,
    sigmaRatBallNeg, sigmaRatBallPow, sigmaRatBallConst,
    sigmaC00495CoefficientBall, Finset.sum_range_succ]

theorem sigmaC01Minor_lower_pos :
    ∀ s < 9, 0 < sigmaRatBallLower
      (sigmaFiniteScaledMomentBallMinor sigmaC01CoefficientBall s) := by
  intro s hs
  interval_cases s <;>
    norm_num [sigmaRatBallLower, sigmaFiniteScaledMomentBallMinor,
      sigmaRatBallSub, sigmaFiniteScaledMomentBall, sigmaRatBallMul,
      sigmaRatBallNeg, sigmaRatBallPow, sigmaRatBallConst,
      sigmaC01CoefficientBall, Finset.sum_range_succ]

theorem sigmaC01Minor_final_neg :
    sigmaRatBallUpper
      (sigmaFiniteScaledMomentBallMinor sigmaC01CoefficientBall 9) < 0 := by
  norm_num [sigmaRatBallUpper, sigmaFiniteScaledMomentBallMinor,
    sigmaRatBallSub, sigmaFiniteScaledMomentBall, sigmaRatBallMul,
    sigmaRatBallNeg, sigmaRatBallPow, sigmaRatBallConst,
    sigmaC01CoefficientBall, Finset.sum_range_succ]

end
end CarrySigmaObstruction

#print axioms CarrySigmaObstruction.sigmaC00495Minor_lower_pos
#print axioms CarrySigmaObstruction.sigmaC00495Minor_final_neg
#print axioms CarrySigmaObstruction.sigmaC01Minor_lower_pos
#print axioms CarrySigmaObstruction.sigmaC01Minor_final_neg
