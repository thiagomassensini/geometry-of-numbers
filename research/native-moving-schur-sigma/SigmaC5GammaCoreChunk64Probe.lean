import SigmaC5GammaCoreNodePilot
import Mathlib.Tactic

open SigmaC5Gamma ZetaLean ZetaLean.ComplexInterval
open scoped BigOperators

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def c5GammaCoreChunk64 (i : ℕ) : ℚ :=
  ((∑ k ∈ Finset.range 64,
    ratGammaTerm 240 (1 / 5) 0 (64 * i + k)).1) * (2 : ℚ) ^ 1024

#eval s!"chunk64.floors={((List.range 16).map fun i => Int.floor (c5GammaCoreChunk64 i))}"
