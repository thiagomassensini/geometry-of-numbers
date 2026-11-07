import SigmaC5GammaRationalCore

namespace SigmaC5Gamma

open scoped BigOperators

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def c5GammaSecondRealPointChunk64 (i : ℕ) : ℚ :=
  ((∑ k ∈ Finset.range 64,
    ratGammaTerm 240 (901 / 4000) 0 (64 * i + k)).1) * (2 : ℚ) ^ 1024

#eval s!"gamma-real-901-4000.chunk64.floors={((List.range 16).map fun i => Int.floor (c5GammaSecondRealPointChunk64 i))}"

end SigmaC5Gamma
