import SigmaC5GammaRationalCore
import Mathlib.Tactic

namespace SigmaC5Gamma
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def c5GammaComplexNodeUpperChunk64 (i : ℕ) : RatComplex :=
  let z := ∑ k ∈ Finset.range 64,
    ratGammaTerm 240 (1099 / 4000) (3 / 20) (64 * i + k)
  (z.1 * (2 : ℚ) ^ 1024, z.2 * (2 : ℚ) ^ 1024)

#eval s!"gamma-complex-node-1099-4000-3i-20.real-floors={((List.range 16).map fun i => Int.floor (c5GammaComplexNodeUpperChunk64 i).1)}"
#eval s!"gamma-complex-node-1099-4000-3i-20.imag-floors={((List.range 16).map fun i => Int.floor (c5GammaComplexNodeUpperChunk64 i).2)}"

end SigmaC5Gamma
