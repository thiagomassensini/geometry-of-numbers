import SigmaC5GammaSecondRealPointCertificate
import Mathlib.Tactic

open SigmaC5Gamma
open scoped BigOperators

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def c5GammaSecondRealPointCore : SigmaC5Gamma.RatComplex :=
  SigmaC5Gamma.gammaFiniteRationalCore 1024 240 (901 / 4000) 0

def c5GammaSecondRealPointCoreScaled : ℚ :=
  c5GammaSecondRealPointCore.1 * (2 : ℚ) ^ 1024

private def c5GammaCoreTermReal (k : ℕ) : ℚ :=
  (ratGammaTerm 240 (901 / 4000) 0 k).1

private def c5GammaSecondRealPointChunkFloor (i : ℕ) : ℤ :=
  Int.floor (c5GammaSecondRealPointChunk64 i)

private theorem c5GammaSecondRealPointSumRangeBlocks (f : ℕ → ℚ) (n : ℕ) :
    (∑ k ∈ Finset.range (64 * n), f k) =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range 64, f (64 * i + j) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih]
      simp only [Finset.sum_range_succ]

theorem c5GammaSecondRealPointCoreScaled_eq_chunkSum :
    c5GammaSecondRealPointCoreScaled =
      ∑ i ∈ Finset.range 16, c5GammaSecondRealPointChunk64 i := by
  change
    (∑ k ∈ Finset.range 1024, (ratGammaTerm 240 (901 / 4000) 0 k).1) *
      (2 : ℚ) ^ 1024 =
    ∑ i ∈ Finset.range 16,
      ((∑ j ∈ Finset.range 64,
          (ratGammaTerm 240 (901 / 4000) 0 (64 * i + j)).1) * (2 : ℚ) ^ 1024)
  have h1024 : 1024 = 64 * 16 := by norm_num
  calc
    _ = (∑ k ∈ Finset.range (64 * 16),
        (ratGammaTerm 240 (901 / 4000) 0 k).1) * (2 : ℚ) ^ 1024 := by rw [h1024]
    _ = (∑ i ∈ Finset.range 16, ∑ j ∈ Finset.range 64,
        (ratGammaTerm 240 (901 / 4000) 0 (64 * i + j)).1) * (2 : ℚ) ^ 1024 := by
          congr 1
          exact c5GammaSecondRealPointSumRangeBlocks
            (fun k => (ratGammaTerm 240 (901 / 4000) 0 k).1) 16
    _ = ∑ i ∈ Finset.range 16,
        ((∑ j ∈ Finset.range 64,
          (ratGammaTerm 240 (901 / 4000) 0 (64 * i + j)).1) * (2 : ℚ) ^ 1024) := by
          rw [Finset.sum_mul]

theorem c5GammaSecondRealPointCoreScaled_chunkBounds :
    (∑ i ∈ Finset.range 16, (c5GammaSecondRealPointChunkFloor i : ℚ)) ≤
      c5GammaSecondRealPointCoreScaled ∧
    c5GammaSecondRealPointCoreScaled <
      ∑ i ∈ Finset.range 16, ((c5GammaSecondRealPointChunkFloor i : ℚ) + 1) := by
  rw [c5GammaSecondRealPointCoreScaled_eq_chunkSum]
  constructor
  · apply Finset.sum_le_sum
    intro i hi
    exact_mod_cast Int.floor_le (c5GammaSecondRealPointChunk64 i)
  · apply Finset.sum_lt_sum
    · intro i hi
      exact_mod_cast (Int.lt_floor_add_one (c5GammaSecondRealPointChunk64 i)).le
    · exact ⟨0, by simp, by exact_mod_cast Int.lt_floor_add_one (c5GammaSecondRealPointChunk64 0)⟩

#print axioms c5GammaSecondRealPointCoreScaled_eq_chunkSum
#print axioms c5GammaSecondRealPointCoreScaled_chunkBounds


theorem c5GammaSecondRealPointChunkFloorSum_eq :
    (∑ i ∈ Finset.range 16, (c5GammaSecondRealPointChunkFloor i : ℚ)) = (211755574561757541666103936004176491019922474439950111197804961570606984840393171965702517160604229504006435781882476270787841186285575834374632727758719297435674824955611337746445354905970244153722884734818301797777825213827613431884565478631662213832586245714269979802436660380037035072231085022641554800542 : ℚ) := by
  norm_num [c5GammaSecondRealPointChunkFloor, c5GammaSecondRealPointChunk64_0_floor,
    c5GammaSecondRealPointChunk64_1_floor,
    c5GammaSecondRealPointChunk64_2_floor,
    c5GammaSecondRealPointChunk64_3_floor,
    c5GammaSecondRealPointChunk64_4_floor,
    c5GammaSecondRealPointChunk64_5_floor,
    c5GammaSecondRealPointChunk64_6_floor,
    c5GammaSecondRealPointChunk64_7_floor,
    c5GammaSecondRealPointChunk64_8_floor,
    c5GammaSecondRealPointChunk64_9_floor,
    c5GammaSecondRealPointChunk64_10_floor,
    c5GammaSecondRealPointChunk64_11_floor,
    c5GammaSecondRealPointChunk64_12_floor,
    c5GammaSecondRealPointChunk64_13_floor,
    c5GammaSecondRealPointChunk64_14_floor,
    c5GammaSecondRealPointChunk64_15_floor, Finset.sum_range_succ]


def c5GammaSecondRealPointCoreChunkBox : ZetaLean.ComplexInterval :=
  { re := { lo := (211755574561757541666103936004176491019922474439950111197804961570606984840393171965702517160604229504006435781882476270787841186285575834374632727758719297435674824955611337746445354905970244153722884734818301797777825213827613431884565478631662213832586245714269979802436660380037035072231085022641554800542 : ℚ) / (2 : ℚ) ^ 1024,
            hi := (211755574561757541666103936004176491019922474439950111197804961570606984840393171965702517160604229504006435781882476270787841186285575834374632727758719297435674824955611337746445354905970244153722884734818301797777825213827613431884565478631662213832586245714269979802436660380037035072231085022641554800558 : ℚ) / (2 : ℚ) ^ 1024,
            le := by
              have hnum : (211755574561757541666103936004176491019922474439950111197804961570606984840393171965702517160604229504006435781882476270787841186285575834374632727758719297435674824955611337746445354905970244153722884734818301797777825213827613431884565478631662213832586245714269979802436660380037035072231085022641554800542 : ℚ) ≤ (211755574561757541666103936004176491019922474439950111197804961570606984840393171965702517160604229504006435781882476270787841186285575834374632727758719297435674824955611337746445354905970244153722884734818301797777825213827613431884565478631662213832586245714269979802436660380037035072231085022641554800558 : ℚ) := by norm_num
              exact div_le_div_of_nonneg_right hnum (by positivity) },
    im := ZetaLean.Interval.exact 0 }

theorem c5GammaSecondRealPointCoreChunkBox_contains :
    c5GammaSecondRealPointCoreChunkBox.contains
      (ratComplexToComplex c5GammaSecondRealPointCore) := by
  have hbounds := c5GammaSecondRealPointCoreScaled_chunkBounds
  have hlo : (211755574561757541666103936004176491019922474439950111197804961570606984840393171965702517160604229504006435781882476270787841186285575834374632727758719297435674824955611337746445354905970244153722884734818301797777825213827613431884565478631662213832586245714269979802436660380037035072231085022641554800542 : ℚ) ≤ c5GammaSecondRealPointCoreScaled := by
    simpa [c5GammaSecondRealPointChunkFloorSum_eq] using hbounds.1
  have hhi : c5GammaSecondRealPointCoreScaled < (211755574561757541666103936004176491019922474439950111197804961570606984840393171965702517160604229504006435781882476270787841186285575834374632727758719297435674824955611337746445354905970244153722884734818301797777825213827613431884565478631662213832586245714269979802436660380037035072231085022641554800558 : ℚ) := by
    calc
      c5GammaSecondRealPointCoreScaled <
          ∑ i ∈ Finset.range 16, ((c5GammaSecondRealPointChunkFloor i : ℚ) + 1) := hbounds.2
      _ = (211755574561757541666103936004176491019922474439950111197804961570606984840393171965702517160604229504006435781882476270787841186285575834374632727758719297435674824955611337746445354905970244153722884734818301797777825213827613431884565478631662213832586245714269979802436660380037035072231085022641554800542 : ℚ) + 16 := by
        rw [Finset.sum_add_distrib, c5GammaSecondRealPointChunkFloorSum_eq]
        norm_num
      _ = (211755574561757541666103936004176491019922474439950111197804961570606984840393171965702517160604229504006435781882476270787841186285575834374632727758719297435674824955611337746445354905970244153722884734818301797777825213827613431884565478631662213832586245714269979802436660380037035072231085022641554800558 : ℚ) := by norm_num
  have hden : (0 : ℚ) < (2 : ℚ) ^ 1024 := by positivity
  have hqlo : (211755574561757541666103936004176491019922474439950111197804961570606984840393171965702517160604229504006435781882476270787841186285575834374632727758719297435674824955611337746445354905970244153722884734818301797777825213827613431884565478631662213832586245714269979802436660380037035072231085022641554800542 : ℚ) / (2 : ℚ) ^ 1024 ≤ c5GammaSecondRealPointCore.1 := by
    rw [div_le_iff₀ hden]
    simpa [c5GammaSecondRealPointCoreScaled] using hlo
  have hqhi : c5GammaSecondRealPointCore.1 ≤ (211755574561757541666103936004176491019922474439950111197804961570606984840393171965702517160604229504006435781882476270787841186285575834374632727758719297435674824955611337746445354905970244153722884734818301797777825213827613431884565478631662213832586245714269979802436660380037035072231085022641554800558 : ℚ) / (2 : ℚ) ^ 1024 := by
    rw [le_div_iff₀ hden]
    have hh : c5GammaSecondRealPointCore.1 * (2 : ℚ) ^ 1024 < (211755574561757541666103936004176491019922474439950111197804961570606984840393171965702517160604229504006435781882476270787841186285575834374632727758719297435674824955611337746445354905970244153722884734818301797777825213827613431884565478631662213832586245714269979802436660380037035072231085022641554800558 : ℚ) := by
      simpa [c5GammaSecondRealPointCoreScaled] using hhi
    exact le_of_lt hh
  have him : c5GammaSecondRealPointCore.2 = 0 := by
    change (∑ k ∈ Finset.range 1024, (ratGammaTerm 240 (901 / 4000) 0 k).2) = 0
    apply Finset.sum_eq_zero
    intro k hk
    simp [ratGammaTerm, ratComplexInv, ratComplexMul]
  simp only [ZetaLean.ComplexInterval.contains, ZetaLean.Interval.contains,
    c5GammaSecondRealPointCoreChunkBox, ZetaLean.Interval.exact, ratComplexToComplex]
  constructor
  · constructor
    · exact_mod_cast hqlo
    · exact_mod_cast hqhi
  · simp [him]

#print axioms c5GammaSecondRealPointChunkFloorSum_eq
#print axioms c5GammaSecondRealPointCoreChunkBox_contains
