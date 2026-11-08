import SigmaC5GammaComplexNodeDOneUpperComplexCertificate
import Mathlib.Tactic

open SigmaC5Gamma ZetaLean ZetaLean.ComplexInterval
open scoped BigOperators

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option exponentiation.threshold 2048

def c5GammaComplexNodeDOneUpperComplexCore : RatComplex :=
  gammaFiniteRationalCore 1024 240 (3 / 10) (3 / 20)

def c5GammaComplexNodeDOneUpperComplexCoreScaledReal : ℚ :=
  c5GammaComplexNodeDOneUpperComplexCore.1 * (2 : ℚ) ^ 1024

def c5GammaComplexNodeDOneUpperComplexCoreScaledImag : ℚ :=
  c5GammaComplexNodeDOneUpperComplexCore.2 * (2 : ℚ) ^ 1024

def c5GammaComplexNodeDOneUpperComplexRealFloor (i : ℕ) : ℤ :=
  Int.floor (c5GammaComplexNodeDOneUpperComplexChunk64 i).1

def c5GammaComplexNodeDOneUpperComplexImagFloor (i : ℕ) : ℤ :=
  Int.floor (c5GammaComplexNodeDOneUpperComplexChunk64 i).2

private theorem c5GammaComplexNodeDOneUpperComplexSumRangeBlocks (f : ℕ → ℚ) (n : ℕ) :
    (∑ k ∈ Finset.range (64 * n), f k) =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range 64, f (64 * i + j) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih]
      simp only [Finset.sum_range_succ]

theorem c5GammaComplexNodeDOneUpperComplexCoreScaledReal_eq_chunkSum :
    c5GammaComplexNodeDOneUpperComplexCoreScaledReal =
      ∑ i ∈ Finset.range 16, (c5GammaComplexNodeDOneUpperComplexChunk64 i).1 := by
  change
    (∑ k ∈ Finset.range 1024,
      (ratGammaTerm 240 (3 / 10) (3 / 20) k).1) * (2 : ℚ) ^ 1024 =
    ∑ i ∈ Finset.range 16,
      ((∑ j ∈ Finset.range 64,
        (ratGammaTerm 240 (3 / 10) (3 / 20) (64 * i + j)).1) * (2 : ℚ) ^ 1024)
  have h1024 : 1024 = 64 * 16 := by norm_num
  calc
    _ = (∑ k ∈ Finset.range (64 * 16),
        (ratGammaTerm 240 (3 / 10) (3 / 20) k).1) * (2 : ℚ) ^ 1024 := by rw [h1024]
    _ = (∑ i ∈ Finset.range 16, ∑ j ∈ Finset.range 64,
        (ratGammaTerm 240 (3 / 10) (3 / 20) (64 * i + j)).1) * (2 : ℚ) ^ 1024 := by
          congr 1
          exact c5GammaComplexNodeDOneUpperComplexSumRangeBlocks
            (fun k => (ratGammaTerm 240 (3 / 10) (3 / 20) k).1) 16
    _ = ∑ i ∈ Finset.range 16,
        ((∑ j ∈ Finset.range 64,
          (ratGammaTerm 240 (3 / 10) (3 / 20) (64 * i + j)).1) * (2 : ℚ) ^ 1024) := by
          rw [Finset.sum_mul]

theorem c5GammaComplexNodeDOneUpperComplexCoreScaledImag_eq_chunkSum :
    c5GammaComplexNodeDOneUpperComplexCoreScaledImag =
      ∑ i ∈ Finset.range 16, (c5GammaComplexNodeDOneUpperComplexChunk64 i).2 := by
  change
    (∑ k ∈ Finset.range 1024,
      (ratGammaTerm 240 (3 / 10) (3 / 20) k).2) * (2 : ℚ) ^ 1024 =
    ∑ i ∈ Finset.range 16,
      ((∑ j ∈ Finset.range 64,
        (ratGammaTerm 240 (3 / 10) (3 / 20) (64 * i + j)).2) * (2 : ℚ) ^ 1024)
  have h1024 : 1024 = 64 * 16 := by norm_num
  calc
    _ = (∑ k ∈ Finset.range (64 * 16),
        (ratGammaTerm 240 (3 / 10) (3 / 20) k).2) * (2 : ℚ) ^ 1024 := by rw [h1024]
    _ = (∑ i ∈ Finset.range 16, ∑ j ∈ Finset.range 64,
        (ratGammaTerm 240 (3 / 10) (3 / 20) (64 * i + j)).2) * (2 : ℚ) ^ 1024 := by
          congr 1
          exact c5GammaComplexNodeDOneUpperComplexSumRangeBlocks
            (fun k => (ratGammaTerm 240 (3 / 10) (3 / 20) k).2) 16
    _ = ∑ i ∈ Finset.range 16,
        ((∑ j ∈ Finset.range 64,
          (ratGammaTerm 240 (3 / 10) (3 / 20) (64 * i + j)).2) * (2 : ℚ) ^ 1024) := by
          rw [Finset.sum_mul]

theorem c5GammaComplexNodeDOneUpperComplexCoreScaled_chunkBounds :
    (∑ i ∈ Finset.range 16, (c5GammaComplexNodeDOneUpperComplexRealFloor i : ℚ)) ≤
      c5GammaComplexNodeDOneUpperComplexCoreScaledReal ∧
    c5GammaComplexNodeDOneUpperComplexCoreScaledReal <
      ∑ i ∈ Finset.range 16, ((c5GammaComplexNodeDOneUpperComplexRealFloor i : ℚ) + 1) ∧
    (∑ i ∈ Finset.range 16, (c5GammaComplexNodeDOneUpperComplexImagFloor i : ℚ)) ≤
      c5GammaComplexNodeDOneUpperComplexCoreScaledImag ∧
    c5GammaComplexNodeDOneUpperComplexCoreScaledImag <
      ∑ i ∈ Finset.range 16, ((c5GammaComplexNodeDOneUpperComplexImagFloor i : ℚ) + 1) := by
  constructor
  · rw [c5GammaComplexNodeDOneUpperComplexCoreScaledReal_eq_chunkSum]
    apply Finset.sum_le_sum
    intro i hi
    exact_mod_cast Int.floor_le (c5GammaComplexNodeDOneUpperComplexChunk64 i).1
  constructor
  · rw [c5GammaComplexNodeDOneUpperComplexCoreScaledReal_eq_chunkSum]
    apply Finset.sum_lt_sum
    · intro i hi
      exact_mod_cast (Int.lt_floor_add_one (c5GammaComplexNodeDOneUpperComplexChunk64 i).1).le
    · exact ⟨0, by simp, by exact_mod_cast Int.lt_floor_add_one (c5GammaComplexNodeDOneUpperComplexChunk64 0).1⟩
  constructor
  · rw [c5GammaComplexNodeDOneUpperComplexCoreScaledImag_eq_chunkSum]
    apply Finset.sum_le_sum
    intro i hi
    exact_mod_cast Int.floor_le (c5GammaComplexNodeDOneUpperComplexChunk64 i).2
  · rw [c5GammaComplexNodeDOneUpperComplexCoreScaledImag_eq_chunkSum]
    apply Finset.sum_lt_sum
    · intro i hi
      exact_mod_cast (Int.lt_floor_add_one (c5GammaComplexNodeDOneUpperComplexChunk64 i).2).le
    · exact ⟨0, by simp, by exact_mod_cast Int.lt_floor_add_one (c5GammaComplexNodeDOneUpperComplexChunk64 0).2⟩

#print axioms c5GammaComplexNodeDOneUpperComplexCoreScaledReal_eq_chunkSum
#print axioms c5GammaComplexNodeDOneUpperComplexCoreScaledImag_eq_chunkSum
#print axioms c5GammaComplexNodeDOneUpperComplexCoreScaled_chunkBounds

theorem c5GammaComplexNodeDOneUpperComplexRealFloorSum_eq :
    (∑ i ∈ Finset.range 16, (c5GammaComplexNodeDOneUpperComplexRealFloor i : ℚ)) = (23616023308236370709646540533985102290089791949676555586892816069502948240945858159411885622742689395831040014535160167267088491924762717791761209210002244820138122230084929714789952556893970292277991561990443618933016174794656156514130417895754761971572293789168964378172476138581613709734036952152491634715 : ℚ) := by
  norm_num [c5GammaComplexNodeDOneUpperComplexRealFloor,     c5GammaComplexNodeDOneUpperComplexChunk64RealFloor_0,
    c5GammaComplexNodeDOneUpperComplexChunk64RealFloor_1,
    c5GammaComplexNodeDOneUpperComplexChunk64RealFloor_2,
    c5GammaComplexNodeDOneUpperComplexChunk64RealFloor_3,
    c5GammaComplexNodeDOneUpperComplexChunk64RealFloor_4,
    c5GammaComplexNodeDOneUpperComplexChunk64RealFloor_5,
    c5GammaComplexNodeDOneUpperComplexChunk64RealFloor_6,
    c5GammaComplexNodeDOneUpperComplexChunk64RealFloor_7,
    c5GammaComplexNodeDOneUpperComplexChunk64RealFloor_8,
    c5GammaComplexNodeDOneUpperComplexChunk64RealFloor_9,
    c5GammaComplexNodeDOneUpperComplexChunk64RealFloor_10,
    c5GammaComplexNodeDOneUpperComplexChunk64RealFloor_11,
    c5GammaComplexNodeDOneUpperComplexChunk64RealFloor_12,
    c5GammaComplexNodeDOneUpperComplexChunk64RealFloor_13,
    c5GammaComplexNodeDOneUpperComplexChunk64RealFloor_14,
    c5GammaComplexNodeDOneUpperComplexChunk64RealFloor_15, Finset.sum_range_succ]

theorem c5GammaComplexNodeDOneUpperComplexImagFloorSum_eq :
    (∑ i ∈ Finset.range 16, (c5GammaComplexNodeDOneUpperComplexImagFloor i : ℚ)) = (-88652077194414613103010602756068951238628381382776489871252115422080257540484918830188516786272351641814372764125250193961749616454413415393657802046481899794364999997374155734068599826792568152035194751142565217746859464288769780058607053204541679795472490014524358563706466958622097230511777029338623753106 : ℚ) := by
  norm_num [c5GammaComplexNodeDOneUpperComplexImagFloor,     c5GammaComplexNodeDOneUpperComplexChunk64ImagFloor_0,
    c5GammaComplexNodeDOneUpperComplexChunk64ImagFloor_1,
    c5GammaComplexNodeDOneUpperComplexChunk64ImagFloor_2,
    c5GammaComplexNodeDOneUpperComplexChunk64ImagFloor_3,
    c5GammaComplexNodeDOneUpperComplexChunk64ImagFloor_4,
    c5GammaComplexNodeDOneUpperComplexChunk64ImagFloor_5,
    c5GammaComplexNodeDOneUpperComplexChunk64ImagFloor_6,
    c5GammaComplexNodeDOneUpperComplexChunk64ImagFloor_7,
    c5GammaComplexNodeDOneUpperComplexChunk64ImagFloor_8,
    c5GammaComplexNodeDOneUpperComplexChunk64ImagFloor_9,
    c5GammaComplexNodeDOneUpperComplexChunk64ImagFloor_10,
    c5GammaComplexNodeDOneUpperComplexChunk64ImagFloor_11,
    c5GammaComplexNodeDOneUpperComplexChunk64ImagFloor_12,
    c5GammaComplexNodeDOneUpperComplexChunk64ImagFloor_13,
    c5GammaComplexNodeDOneUpperComplexChunk64ImagFloor_14,
    c5GammaComplexNodeDOneUpperComplexChunk64ImagFloor_15, Finset.sum_range_succ]

def c5GammaComplexNodeDOneUpperComplexCoreBox : ZetaLean.ComplexInterval :=
  { re := { lo := (23616023308236370709646540533985102290089791949676555586892816069502948240945858159411885622742689395831040014535160167267088491924762717791761209210002244820138122230084929714789952556893970292277991561990443618933016174794656156514130417895754761971572293789168964378172476138581613709734036952152491634715 : ℚ) / (2 : ℚ) ^ 1024,
            hi := ((23616023308236370709646540533985102290089791949676555586892816069502948240945858159411885622742689395831040014535160167267088491924762717791761209210002244820138122230084929714789952556893970292277991561990443618933016174794656156514130417895754761971572293789168964378172476138581613709734036952152491634715 + 16) : ℚ) / (2 : ℚ) ^ 1024,
            le := by
              have hnum : (23616023308236370709646540533985102290089791949676555586892816069502948240945858159411885622742689395831040014535160167267088491924762717791761209210002244820138122230084929714789952556893970292277991561990443618933016174794656156514130417895754761971572293789168964378172476138581613709734036952152491634715 : ℚ) ≤
                  (23616023308236370709646540533985102290089791949676555586892816069502948240945858159411885622742689395831040014535160167267088491924762717791761209210002244820138122230084929714789952556893970292277991561990443618933016174794656156514130417895754761971572293789168964378172476138581613709734036952152491634715 + 16 : ℚ) := by norm_num
              exact div_le_div_of_nonneg_right hnum (by positivity) },
    im := { lo := (-88652077194414613103010602756068951238628381382776489871252115422080257540484918830188516786272351641814372764125250193961749616454413415393657802046481899794364999997374155734068599826792568152035194751142565217746859464288769780058607053204541679795472490014524358563706466958622097230511777029338623753106 : ℚ) / (2 : ℚ) ^ 1024,
            hi := ((-88652077194414613103010602756068951238628381382776489871252115422080257540484918830188516786272351641814372764125250193961749616454413415393657802046481899794364999997374155734068599826792568152035194751142565217746859464288769780058607053204541679795472490014524358563706466958622097230511777029338623753106 + 16) : ℚ) / (2 : ℚ) ^ 1024,
            le := by
              have hnum : (-88652077194414613103010602756068951238628381382776489871252115422080257540484918830188516786272351641814372764125250193961749616454413415393657802046481899794364999997374155734068599826792568152035194751142565217746859464288769780058607053204541679795472490014524358563706466958622097230511777029338623753106 : ℚ) ≤
                  (-88652077194414613103010602756068951238628381382776489871252115422080257540484918830188516786272351641814372764125250193961749616454413415393657802046481899794364999997374155734068599826792568152035194751142565217746859464288769780058607053204541679795472490014524358563706466958622097230511777029338623753106 + 16 : ℚ) := by norm_num
              exact div_le_div_of_nonneg_right hnum (by positivity) } }

theorem c5GammaComplexNodeDOneUpperComplexCoreBox_contains :
    c5GammaComplexNodeDOneUpperComplexCoreBox.contains (ratComplexToComplex c5GammaComplexNodeDOneUpperComplexCore) := by
  have hbounds := c5GammaComplexNodeDOneUpperComplexCoreScaled_chunkBounds
  have hReLo : (23616023308236370709646540533985102290089791949676555586892816069502948240945858159411885622742689395831040014535160167267088491924762717791761209210002244820138122230084929714789952556893970292277991561990443618933016174794656156514130417895754761971572293789168964378172476138581613709734036952152491634715 : ℚ) ≤ c5GammaComplexNodeDOneUpperComplexCoreScaledReal := by
    simpa [c5GammaComplexNodeDOneUpperComplexRealFloorSum_eq] using hbounds.1
  have hReHi : c5GammaComplexNodeDOneUpperComplexCoreScaledReal < (23616023308236370709646540533985102290089791949676555586892816069502948240945858159411885622742689395831040014535160167267088491924762717791761209210002244820138122230084929714789952556893970292277991561990443618933016174794656156514130417895754761971572293789168964378172476138581613709734036952152491634715 + 16 : ℚ) := by
    calc
      c5GammaComplexNodeDOneUpperComplexCoreScaledReal <
          ∑ i ∈ Finset.range 16, ((c5GammaComplexNodeDOneUpperComplexRealFloor i : ℚ) + 1) := hbounds.2.1
      _ = (23616023308236370709646540533985102290089791949676555586892816069502948240945858159411885622742689395831040014535160167267088491924762717791761209210002244820138122230084929714789952556893970292277991561990443618933016174794656156514130417895754761971572293789168964378172476138581613709734036952152491634715 : ℚ) + 16 := by
        rw [Finset.sum_add_distrib, c5GammaComplexNodeDOneUpperComplexRealFloorSum_eq]
        norm_num
  have hImLo : (-88652077194414613103010602756068951238628381382776489871252115422080257540484918830188516786272351641814372764125250193961749616454413415393657802046481899794364999997374155734068599826792568152035194751142565217746859464288769780058607053204541679795472490014524358563706466958622097230511777029338623753106 : ℚ) ≤ c5GammaComplexNodeDOneUpperComplexCoreScaledImag := by
    simpa [c5GammaComplexNodeDOneUpperComplexImagFloorSum_eq] using hbounds.2.2.1
  have hImHi : c5GammaComplexNodeDOneUpperComplexCoreScaledImag < (-88652077194414613103010602756068951238628381382776489871252115422080257540484918830188516786272351641814372764125250193961749616454413415393657802046481899794364999997374155734068599826792568152035194751142565217746859464288769780058607053204541679795472490014524358563706466958622097230511777029338623753106 + 16 : ℚ) := by
    calc
      c5GammaComplexNodeDOneUpperComplexCoreScaledImag <
          ∑ i ∈ Finset.range 16, ((c5GammaComplexNodeDOneUpperComplexImagFloor i : ℚ) + 1) := hbounds.2.2.2
      _ = (-88652077194414613103010602756068951238628381382776489871252115422080257540484918830188516786272351641814372764125250193961749616454413415393657802046481899794364999997374155734068599826792568152035194751142565217746859464288769780058607053204541679795472490014524358563706466958622097230511777029338623753106 : ℚ) + 16 := by
        rw [Finset.sum_add_distrib, c5GammaComplexNodeDOneUpperComplexImagFloorSum_eq]
        norm_num
  have hden : (0 : ℚ) < (2 : ℚ) ^ 1024 := by positivity
  have hqloRe : (23616023308236370709646540533985102290089791949676555586892816069502948240945858159411885622742689395831040014535160167267088491924762717791761209210002244820138122230084929714789952556893970292277991561990443618933016174794656156514130417895754761971572293789168964378172476138581613709734036952152491634715 : ℚ) / (2 : ℚ) ^ 1024 ≤ c5GammaComplexNodeDOneUpperComplexCore.1 := by
    rw [div_le_iff₀ hden]
    simpa [c5GammaComplexNodeDOneUpperComplexCoreScaledReal] using hReLo
  have hqhiRe : c5GammaComplexNodeDOneUpperComplexCore.1 ≤ (23616023308236370709646540533985102290089791949676555586892816069502948240945858159411885622742689395831040014535160167267088491924762717791761209210002244820138122230084929714789952556893970292277991561990443618933016174794656156514130417895754761971572293789168964378172476138581613709734036952152491634715 + 16 : ℚ) / (2 : ℚ) ^ 1024 := by
    rw [le_div_iff₀ hden]
    have hh : c5GammaComplexNodeDOneUpperComplexCore.1 * (2 : ℚ) ^ 1024 < (23616023308236370709646540533985102290089791949676555586892816069502948240945858159411885622742689395831040014535160167267088491924762717791761209210002244820138122230084929714789952556893970292277991561990443618933016174794656156514130417895754761971572293789168964378172476138581613709734036952152491634715 + 16 : ℚ) := by
      simpa [c5GammaComplexNodeDOneUpperComplexCoreScaledReal] using hReHi
    exact le_of_lt hh
  have hqloIm : (-88652077194414613103010602756068951238628381382776489871252115422080257540484918830188516786272351641814372764125250193961749616454413415393657802046481899794364999997374155734068599826792568152035194751142565217746859464288769780058607053204541679795472490014524358563706466958622097230511777029338623753106 : ℚ) / (2 : ℚ) ^ 1024 ≤ c5GammaComplexNodeDOneUpperComplexCore.2 := by
    rw [div_le_iff₀ hden]
    simpa [c5GammaComplexNodeDOneUpperComplexCoreScaledImag] using hImLo
  have hqhiIm : c5GammaComplexNodeDOneUpperComplexCore.2 ≤ (-88652077194414613103010602756068951238628381382776489871252115422080257540484918830188516786272351641814372764125250193961749616454413415393657802046481899794364999997374155734068599826792568152035194751142565217746859464288769780058607053204541679795472490014524358563706466958622097230511777029338623753106 + 16 : ℚ) / (2 : ℚ) ^ 1024 := by
    rw [le_div_iff₀ hden]
    have hh : c5GammaComplexNodeDOneUpperComplexCore.2 * (2 : ℚ) ^ 1024 < (-88652077194414613103010602756068951238628381382776489871252115422080257540484918830188516786272351641814372764125250193961749616454413415393657802046481899794364999997374155734068599826792568152035194751142565217746859464288769780058607053204541679795472490014524358563706466958622097230511777029338623753106 + 16 : ℚ) := by
      simpa [c5GammaComplexNodeDOneUpperComplexCoreScaledImag] using hImHi
    exact le_of_lt hh
  simp only [ZetaLean.ComplexInterval.contains, ZetaLean.Interval.contains,
    c5GammaComplexNodeDOneUpperComplexCoreBox, ratComplexToComplex]
  constructor
  · constructor
    · exact_mod_cast hqloRe
    · exact_mod_cast hqhiRe
  · constructor
    · exact_mod_cast hqloIm
    · exact_mod_cast hqhiIm

#print axioms c5GammaComplexNodeDOneUpperComplexRealFloorSum_eq
#print axioms c5GammaComplexNodeDOneUpperComplexImagFloorSum_eq
#print axioms c5GammaComplexNodeDOneUpperComplexCoreBox_contains
