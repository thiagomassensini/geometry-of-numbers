import GammaCoefficients
namespace CarryOddHeadSource
open CarryC3Gamma
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024

/-- Rational centers for exact finite Gamma evaluation, not source assumptions. -/
def gammaCoefficientSevenCenter : ℚ :=
  6552493551000305123069468322266214786 / 10^32
def gammaCoefficientEightCenter : ℚ :=
  26213444349175361348997974840310130503 / 10^32

theorem gamma_coefficient_seven_box :
    |rationalCoefficient 512 7 - gammaCoefficientSevenCenter| ≤ (1/10^30:ℚ) := by
  decide +kernel

theorem gamma_coefficient_eight_box :
    |rationalCoefficient 512 8 - gammaCoefficientEightCenter| ≤ (1/10^30:ℚ) := by
  decide +kernel

#print axioms gamma_coefficient_seven_box
#print axioms gamma_coefficient_eight_box
end CarryOddHeadSource
