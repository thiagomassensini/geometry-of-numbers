import SigmaC5GammaComplexNodeDOneComplexCertificate
import Mathlib.Tactic

open SigmaC5Gamma ZetaLean ZetaLean.ComplexInterval
open scoped BigOperators

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option exponentiation.threshold 2048

def c5GammaComplexNodeDOneComplexCore : RatComplex :=
  gammaFiniteRationalCore 1024 240 (1 / 5) (3 / 20)

def c5GammaComplexNodeDOneComplexCoreScaledReal : ℚ :=
  c5GammaComplexNodeDOneComplexCore.1 * (2 : ℚ) ^ 1024

def c5GammaComplexNodeDOneComplexCoreScaledImag : ℚ :=
  c5GammaComplexNodeDOneComplexCore.2 * (2 : ℚ) ^ 1024

def c5GammaComplexNodeDOneComplexRealFloor (i : ℕ) : ℤ :=
  Int.floor (c5GammaComplexNodeDOneComplexChunk64 i).1

def c5GammaComplexNodeDOneComplexImagFloor (i : ℕ) : ℤ :=
  Int.floor (c5GammaComplexNodeDOneComplexChunk64 i).2

private theorem c5GammaComplexNodeDOneComplexSumRangeBlocks (f : ℕ → ℚ) (n : ℕ) :
    (∑ k ∈ Finset.range (64 * n), f k) =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range 64, f (64 * i + j) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih]
      simp only [Finset.sum_range_succ]

theorem c5GammaComplexNodeDOneComplexCoreScaledReal_eq_chunkSum :
    c5GammaComplexNodeDOneComplexCoreScaledReal =
      ∑ i ∈ Finset.range 16, (c5GammaComplexNodeDOneComplexChunk64 i).1 := by
  change
    (∑ k ∈ Finset.range 1024,
      (ratGammaTerm 240 (1 / 5) (3 / 20) k).1) * (2 : ℚ) ^ 1024 =
    ∑ i ∈ Finset.range 16,
      ((∑ j ∈ Finset.range 64,
        (ratGammaTerm 240 (1 / 5) (3 / 20) (64 * i + j)).1) * (2 : ℚ) ^ 1024)
  have h1024 : 1024 = 64 * 16 := by norm_num
  calc
    _ = (∑ k ∈ Finset.range (64 * 16),
        (ratGammaTerm 240 (1 / 5) (3 / 20) k).1) * (2 : ℚ) ^ 1024 := by rw [h1024]
    _ = (∑ i ∈ Finset.range 16, ∑ j ∈ Finset.range 64,
        (ratGammaTerm 240 (1 / 5) (3 / 20) (64 * i + j)).1) * (2 : ℚ) ^ 1024 := by
          congr 1
          exact c5GammaComplexNodeDOneComplexSumRangeBlocks
            (fun k => (ratGammaTerm 240 (1 / 5) (3 / 20) k).1) 16
    _ = ∑ i ∈ Finset.range 16,
        ((∑ j ∈ Finset.range 64,
          (ratGammaTerm 240 (1 / 5) (3 / 20) (64 * i + j)).1) * (2 : ℚ) ^ 1024) := by
          rw [Finset.sum_mul]

theorem c5GammaComplexNodeDOneComplexCoreScaledImag_eq_chunkSum :
    c5GammaComplexNodeDOneComplexCoreScaledImag =
      ∑ i ∈ Finset.range 16, (c5GammaComplexNodeDOneComplexChunk64 i).2 := by
  change
    (∑ k ∈ Finset.range 1024,
      (ratGammaTerm 240 (1 / 5) (3 / 20) k).2) * (2 : ℚ) ^ 1024 =
    ∑ i ∈ Finset.range 16,
      ((∑ j ∈ Finset.range 64,
        (ratGammaTerm 240 (1 / 5) (3 / 20) (64 * i + j)).2) * (2 : ℚ) ^ 1024)
  have h1024 : 1024 = 64 * 16 := by norm_num
  calc
    _ = (∑ k ∈ Finset.range (64 * 16),
        (ratGammaTerm 240 (1 / 5) (3 / 20) k).2) * (2 : ℚ) ^ 1024 := by rw [h1024]
    _ = (∑ i ∈ Finset.range 16, ∑ j ∈ Finset.range 64,
        (ratGammaTerm 240 (1 / 5) (3 / 20) (64 * i + j)).2) * (2 : ℚ) ^ 1024 := by
          congr 1
          exact c5GammaComplexNodeDOneComplexSumRangeBlocks
            (fun k => (ratGammaTerm 240 (1 / 5) (3 / 20) k).2) 16
    _ = ∑ i ∈ Finset.range 16,
        ((∑ j ∈ Finset.range 64,
          (ratGammaTerm 240 (1 / 5) (3 / 20) (64 * i + j)).2) * (2 : ℚ) ^ 1024) := by
          rw [Finset.sum_mul]

theorem c5GammaComplexNodeDOneComplexCoreScaled_chunkBounds :
    (∑ i ∈ Finset.range 16, (c5GammaComplexNodeDOneComplexRealFloor i : ℚ)) ≤
      c5GammaComplexNodeDOneComplexCoreScaledReal ∧
    c5GammaComplexNodeDOneComplexCoreScaledReal <
      ∑ i ∈ Finset.range 16, ((c5GammaComplexNodeDOneComplexRealFloor i : ℚ) + 1) ∧
    (∑ i ∈ Finset.range 16, (c5GammaComplexNodeDOneComplexImagFloor i : ℚ)) ≤
      c5GammaComplexNodeDOneComplexCoreScaledImag ∧
    c5GammaComplexNodeDOneComplexCoreScaledImag <
      ∑ i ∈ Finset.range 16, ((c5GammaComplexNodeDOneComplexImagFloor i : ℚ) + 1) := by
  constructor
  · rw [c5GammaComplexNodeDOneComplexCoreScaledReal_eq_chunkSum]
    apply Finset.sum_le_sum
    intro i hi
    exact_mod_cast Int.floor_le (c5GammaComplexNodeDOneComplexChunk64 i).1
  constructor
  · rw [c5GammaComplexNodeDOneComplexCoreScaledReal_eq_chunkSum]
    apply Finset.sum_lt_sum
    · intro i hi
      exact_mod_cast (Int.lt_floor_add_one (c5GammaComplexNodeDOneComplexChunk64 i).1).le
    · exact ⟨0, by simp, by exact_mod_cast Int.lt_floor_add_one (c5GammaComplexNodeDOneComplexChunk64 0).1⟩
  constructor
  · rw [c5GammaComplexNodeDOneComplexCoreScaledImag_eq_chunkSum]
    apply Finset.sum_le_sum
    intro i hi
    exact_mod_cast Int.floor_le (c5GammaComplexNodeDOneComplexChunk64 i).2
  · rw [c5GammaComplexNodeDOneComplexCoreScaledImag_eq_chunkSum]
    apply Finset.sum_lt_sum
    · intro i hi
      exact_mod_cast (Int.lt_floor_add_one (c5GammaComplexNodeDOneComplexChunk64 i).2).le
    · exact ⟨0, by simp, by exact_mod_cast Int.lt_floor_add_one (c5GammaComplexNodeDOneComplexChunk64 0).2⟩

#print axioms c5GammaComplexNodeDOneComplexCoreScaledReal_eq_chunkSum
#print axioms c5GammaComplexNodeDOneComplexCoreScaledImag_eq_chunkSum
#print axioms c5GammaComplexNodeDOneComplexCoreScaled_chunkBounds

theorem c5GammaComplexNodeDOneComplexRealFloorSum_eq :
    (∑ i ∈ Finset.range 16, (c5GammaComplexNodeDOneComplexRealFloor i : ℚ)) = (13622516973689844018855000438402341864238312004240460730078047141822344706708485273712007782269633949226278303812988973529403181135318193564446307898110004307742469490931709870880459638233151578568523776815115017246680818901849029148556413610128520781917485915364003626099118009451258313258546274644665238283 : ℚ) := by
  norm_num [c5GammaComplexNodeDOneComplexRealFloor,     c5GammaComplexNodeDOneComplexChunk64RealFloor_0,
    c5GammaComplexNodeDOneComplexChunk64RealFloor_1,
    c5GammaComplexNodeDOneComplexChunk64RealFloor_2,
    c5GammaComplexNodeDOneComplexChunk64RealFloor_3,
    c5GammaComplexNodeDOneComplexChunk64RealFloor_4,
    c5GammaComplexNodeDOneComplexChunk64RealFloor_5,
    c5GammaComplexNodeDOneComplexChunk64RealFloor_6,
    c5GammaComplexNodeDOneComplexChunk64RealFloor_7,
    c5GammaComplexNodeDOneComplexChunk64RealFloor_8,
    c5GammaComplexNodeDOneComplexChunk64RealFloor_9,
    c5GammaComplexNodeDOneComplexChunk64RealFloor_10,
    c5GammaComplexNodeDOneComplexChunk64RealFloor_11,
    c5GammaComplexNodeDOneComplexChunk64RealFloor_12,
    c5GammaComplexNodeDOneComplexChunk64RealFloor_13,
    c5GammaComplexNodeDOneComplexChunk64RealFloor_14,
    c5GammaComplexNodeDOneComplexChunk64RealFloor_15, Finset.sum_range_succ]

theorem c5GammaComplexNodeDOneComplexImagFloorSum_eq :
    (∑ i ∈ Finset.range 16, (c5GammaComplexNodeDOneComplexImagFloor i : ℚ)) = (-217089949443654355004605353716691023133100234707187310353222685299791800862360950386279021061414059617186330398688985542908603595057036324935745117170746671197526302554242270672370095105688200432910466429162564185168979792385115418978810747023366830007974473883646606425270059699709281308115061607205691977231 : ℚ) := by
  norm_num [c5GammaComplexNodeDOneComplexImagFloor,     c5GammaComplexNodeDOneComplexChunk64ImagFloor_0,
    c5GammaComplexNodeDOneComplexChunk64ImagFloor_1,
    c5GammaComplexNodeDOneComplexChunk64ImagFloor_2,
    c5GammaComplexNodeDOneComplexChunk64ImagFloor_3,
    c5GammaComplexNodeDOneComplexChunk64ImagFloor_4,
    c5GammaComplexNodeDOneComplexChunk64ImagFloor_5,
    c5GammaComplexNodeDOneComplexChunk64ImagFloor_6,
    c5GammaComplexNodeDOneComplexChunk64ImagFloor_7,
    c5GammaComplexNodeDOneComplexChunk64ImagFloor_8,
    c5GammaComplexNodeDOneComplexChunk64ImagFloor_9,
    c5GammaComplexNodeDOneComplexChunk64ImagFloor_10,
    c5GammaComplexNodeDOneComplexChunk64ImagFloor_11,
    c5GammaComplexNodeDOneComplexChunk64ImagFloor_12,
    c5GammaComplexNodeDOneComplexChunk64ImagFloor_13,
    c5GammaComplexNodeDOneComplexChunk64ImagFloor_14,
    c5GammaComplexNodeDOneComplexChunk64ImagFloor_15, Finset.sum_range_succ]

def c5GammaComplexNodeDOneComplexCoreBox : ZetaLean.ComplexInterval :=
  { re := { lo := (13622516973689844018855000438402341864238312004240460730078047141822344706708485273712007782269633949226278303812988973529403181135318193564446307898110004307742469490931709870880459638233151578568523776815115017246680818901849029148556413610128520781917485915364003626099118009451258313258546274644665238283 : ℚ) / (2 : ℚ) ^ 1024,
            hi := ((13622516973689844018855000438402341864238312004240460730078047141822344706708485273712007782269633949226278303812988973529403181135318193564446307898110004307742469490931709870880459638233151578568523776815115017246680818901849029148556413610128520781917485915364003626099118009451258313258546274644665238283 + 16) : ℚ) / (2 : ℚ) ^ 1024,
            le := by
              have hnum : (13622516973689844018855000438402341864238312004240460730078047141822344706708485273712007782269633949226278303812988973529403181135318193564446307898110004307742469490931709870880459638233151578568523776815115017246680818901849029148556413610128520781917485915364003626099118009451258313258546274644665238283 : ℚ) ≤
                  (13622516973689844018855000438402341864238312004240460730078047141822344706708485273712007782269633949226278303812988973529403181135318193564446307898110004307742469490931709870880459638233151578568523776815115017246680818901849029148556413610128520781917485915364003626099118009451258313258546274644665238283 + 16 : ℚ) := by norm_num
              exact div_le_div_of_nonneg_right hnum (by positivity) },
    im := { lo := (-217089949443654355004605353716691023133100234707187310353222685299791800862360950386279021061414059617186330398688985542908603595057036324935745117170746671197526302554242270672370095105688200432910466429162564185168979792385115418978810747023366830007974473883646606425270059699709281308115061607205691977231 : ℚ) / (2 : ℚ) ^ 1024,
            hi := ((-217089949443654355004605353716691023133100234707187310353222685299791800862360950386279021061414059617186330398688985542908603595057036324935745117170746671197526302554242270672370095105688200432910466429162564185168979792385115418978810747023366830007974473883646606425270059699709281308115061607205691977231 + 16) : ℚ) / (2 : ℚ) ^ 1024,
            le := by
              have hnum : (-217089949443654355004605353716691023133100234707187310353222685299791800862360950386279021061414059617186330398688985542908603595057036324935745117170746671197526302554242270672370095105688200432910466429162564185168979792385115418978810747023366830007974473883646606425270059699709281308115061607205691977231 : ℚ) ≤
                  (-217089949443654355004605353716691023133100234707187310353222685299791800862360950386279021061414059617186330398688985542908603595057036324935745117170746671197526302554242270672370095105688200432910466429162564185168979792385115418978810747023366830007974473883646606425270059699709281308115061607205691977231 + 16 : ℚ) := by norm_num
              exact div_le_div_of_nonneg_right hnum (by positivity) } }

theorem c5GammaComplexNodeDOneComplexCoreBox_contains :
    c5GammaComplexNodeDOneComplexCoreBox.contains (ratComplexToComplex c5GammaComplexNodeDOneComplexCore) := by
  have hbounds := c5GammaComplexNodeDOneComplexCoreScaled_chunkBounds
  have hReLo : (13622516973689844018855000438402341864238312004240460730078047141822344706708485273712007782269633949226278303812988973529403181135318193564446307898110004307742469490931709870880459638233151578568523776815115017246680818901849029148556413610128520781917485915364003626099118009451258313258546274644665238283 : ℚ) ≤ c5GammaComplexNodeDOneComplexCoreScaledReal := by
    simpa [c5GammaComplexNodeDOneComplexRealFloorSum_eq] using hbounds.1
  have hReHi : c5GammaComplexNodeDOneComplexCoreScaledReal < (13622516973689844018855000438402341864238312004240460730078047141822344706708485273712007782269633949226278303812988973529403181135318193564446307898110004307742469490931709870880459638233151578568523776815115017246680818901849029148556413610128520781917485915364003626099118009451258313258546274644665238283 + 16 : ℚ) := by
    calc
      c5GammaComplexNodeDOneComplexCoreScaledReal <
          ∑ i ∈ Finset.range 16, ((c5GammaComplexNodeDOneComplexRealFloor i : ℚ) + 1) := hbounds.2.1
      _ = (13622516973689844018855000438402341864238312004240460730078047141822344706708485273712007782269633949226278303812988973529403181135318193564446307898110004307742469490931709870880459638233151578568523776815115017246680818901849029148556413610128520781917485915364003626099118009451258313258546274644665238283 : ℚ) + 16 := by
        rw [Finset.sum_add_distrib, c5GammaComplexNodeDOneComplexRealFloorSum_eq]
        norm_num
  have hImLo : (-217089949443654355004605353716691023133100234707187310353222685299791800862360950386279021061414059617186330398688985542908603595057036324935745117170746671197526302554242270672370095105688200432910466429162564185168979792385115418978810747023366830007974473883646606425270059699709281308115061607205691977231 : ℚ) ≤ c5GammaComplexNodeDOneComplexCoreScaledImag := by
    simpa [c5GammaComplexNodeDOneComplexImagFloorSum_eq] using hbounds.2.2.1
  have hImHi : c5GammaComplexNodeDOneComplexCoreScaledImag < (-217089949443654355004605353716691023133100234707187310353222685299791800862360950386279021061414059617186330398688985542908603595057036324935745117170746671197526302554242270672370095105688200432910466429162564185168979792385115418978810747023366830007974473883646606425270059699709281308115061607205691977231 + 16 : ℚ) := by
    calc
      c5GammaComplexNodeDOneComplexCoreScaledImag <
          ∑ i ∈ Finset.range 16, ((c5GammaComplexNodeDOneComplexImagFloor i : ℚ) + 1) := hbounds.2.2.2
      _ = (-217089949443654355004605353716691023133100234707187310353222685299791800862360950386279021061414059617186330398688985542908603595057036324935745117170746671197526302554242270672370095105688200432910466429162564185168979792385115418978810747023366830007974473883646606425270059699709281308115061607205691977231 : ℚ) + 16 := by
        rw [Finset.sum_add_distrib, c5GammaComplexNodeDOneComplexImagFloorSum_eq]
        norm_num
  have hden : (0 : ℚ) < (2 : ℚ) ^ 1024 := by positivity
  have hqloRe : (13622516973689844018855000438402341864238312004240460730078047141822344706708485273712007782269633949226278303812988973529403181135318193564446307898110004307742469490931709870880459638233151578568523776815115017246680818901849029148556413610128520781917485915364003626099118009451258313258546274644665238283 : ℚ) / (2 : ℚ) ^ 1024 ≤ c5GammaComplexNodeDOneComplexCore.1 := by
    rw [div_le_iff₀ hden]
    simpa [c5GammaComplexNodeDOneComplexCoreScaledReal] using hReLo
  have hqhiRe : c5GammaComplexNodeDOneComplexCore.1 ≤ (13622516973689844018855000438402341864238312004240460730078047141822344706708485273712007782269633949226278303812988973529403181135318193564446307898110004307742469490931709870880459638233151578568523776815115017246680818901849029148556413610128520781917485915364003626099118009451258313258546274644665238283 + 16 : ℚ) / (2 : ℚ) ^ 1024 := by
    rw [le_div_iff₀ hden]
    have hh : c5GammaComplexNodeDOneComplexCore.1 * (2 : ℚ) ^ 1024 < (13622516973689844018855000438402341864238312004240460730078047141822344706708485273712007782269633949226278303812988973529403181135318193564446307898110004307742469490931709870880459638233151578568523776815115017246680818901849029148556413610128520781917485915364003626099118009451258313258546274644665238283 + 16 : ℚ) := by
      simpa [c5GammaComplexNodeDOneComplexCoreScaledReal] using hReHi
    exact le_of_lt hh
  have hqloIm : (-217089949443654355004605353716691023133100234707187310353222685299791800862360950386279021061414059617186330398688985542908603595057036324935745117170746671197526302554242270672370095105688200432910466429162564185168979792385115418978810747023366830007974473883646606425270059699709281308115061607205691977231 : ℚ) / (2 : ℚ) ^ 1024 ≤ c5GammaComplexNodeDOneComplexCore.2 := by
    rw [div_le_iff₀ hden]
    simpa [c5GammaComplexNodeDOneComplexCoreScaledImag] using hImLo
  have hqhiIm : c5GammaComplexNodeDOneComplexCore.2 ≤ (-217089949443654355004605353716691023133100234707187310353222685299791800862360950386279021061414059617186330398688985542908603595057036324935745117170746671197526302554242270672370095105688200432910466429162564185168979792385115418978810747023366830007974473883646606425270059699709281308115061607205691977231 + 16 : ℚ) / (2 : ℚ) ^ 1024 := by
    rw [le_div_iff₀ hden]
    have hh : c5GammaComplexNodeDOneComplexCore.2 * (2 : ℚ) ^ 1024 < (-217089949443654355004605353716691023133100234707187310353222685299791800862360950386279021061414059617186330398688985542908603595057036324935745117170746671197526302554242270672370095105688200432910466429162564185168979792385115418978810747023366830007974473883646606425270059699709281308115061607205691977231 + 16 : ℚ) := by
      simpa [c5GammaComplexNodeDOneComplexCoreScaledImag] using hImHi
    exact le_of_lt hh
  simp only [ZetaLean.ComplexInterval.contains, ZetaLean.Interval.contains,
    c5GammaComplexNodeDOneComplexCoreBox, ratComplexToComplex]
  constructor
  · constructor
    · exact_mod_cast hqloRe
    · exact_mod_cast hqhiRe
  · constructor
    · exact_mod_cast hqloIm
    · exact_mod_cast hqhiIm

#print axioms c5GammaComplexNodeDOneComplexRealFloorSum_eq
#print axioms c5GammaComplexNodeDOneComplexImagFloorSum_eq
#print axioms c5GammaComplexNodeDOneComplexCoreBox_contains
