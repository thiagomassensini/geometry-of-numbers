import SigmaC5GammaCoreNodePilot
import Mathlib.Tactic

open SigmaC5Gamma ZetaLean ZetaLean.ComplexInterval
open scoped BigOperators

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def c5GammaChunk0 : ℚ :=
  ((∑ k ∈ Finset.range 32, ratGammaTerm 240 (1 / 5) 0 k).1) * (2 : ℚ) ^ 1024

#eval s!"chunk0.floor={Int.floor c5GammaChunk0}"
#eval s!"chunk0.ceil={Int.ceil c5GammaChunk0}"

theorem c5GammaChunk0_floor : Int.floor c5GammaChunk0 = 0 := by
  norm_num [c5GammaChunk0, ratGammaTerm, ratComplexInv, ratComplexMul,
    Finset.sum_apply, Finset.sum_range_succ]
