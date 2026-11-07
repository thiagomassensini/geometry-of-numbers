import SigmaC5GammaRationalCore
import Mathlib.Tactic

open SigmaC5Gamma

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def c5GammaCoreNodePilot : RatComplex :=
  gammaFiniteRationalCore 3072 620 (1 / 5) 0

def c5GammaCoreNodePilotScaled : ℚ :=
  c5GammaCoreNodePilot.1 * (2 : ℚ) ^ 1024

def c5GammaCoreNodePilotLo : ℤ := Int.floor c5GammaCoreNodePilotScaled
def c5GammaCoreNodePilotHi : ℤ := Int.ceil c5GammaCoreNodePilotScaled

#eval s!"core.lo={c5GammaCoreNodePilotLo}"
#eval s!"core.hi={c5GammaCoreNodePilotHi}"
#eval s!"core.im={c5GammaCoreNodePilot.2}"
