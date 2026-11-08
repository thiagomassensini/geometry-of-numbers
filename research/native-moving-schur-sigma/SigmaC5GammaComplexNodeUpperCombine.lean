import SigmaC5GammaComplexNodeUpperCertificate
import Mathlib.Tactic

open SigmaC5Gamma ZetaLean ZetaLean.ComplexInterval
open scoped BigOperators

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option exponentiation.threshold 2048

def c5GammaComplexNodeUpperCore : RatComplex :=
  gammaFiniteRationalCore 1024 240 (1099 / 4000) (3 / 20)

def c5GammaComplexNodeUpperCoreScaledReal : ℚ :=
  c5GammaComplexNodeUpperCore.1 * (2 : ℚ) ^ 1024

def c5GammaComplexNodeUpperCoreScaledImag : ℚ :=
  c5GammaComplexNodeUpperCore.2 * (2 : ℚ) ^ 1024

def c5GammaComplexNodeUpperRealFloor (i : ℕ) : ℤ :=
  Int.floor (c5GammaComplexNodeUpperChunk64 i).1

def c5GammaComplexNodeUpperImagFloor (i : ℕ) : ℤ :=
  Int.floor (c5GammaComplexNodeUpperChunk64 i).2

private theorem c5GammaComplexNodeUpperSumRangeBlocks (f : ℕ → ℚ) (n : ℕ) :
    (∑ k ∈ Finset.range (64 * n), f k) =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range 64, f (64 * i + j) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih]
      simp only [Finset.sum_range_succ]

theorem c5GammaComplexNodeUpperCoreScaledReal_eq_chunkSum :
    c5GammaComplexNodeUpperCoreScaledReal =
      ∑ i ∈ Finset.range 16, (c5GammaComplexNodeUpperChunk64 i).1 := by
  change
    (∑ k ∈ Finset.range 1024,
      (ratGammaTerm 240 (1099 / 4000) (3 / 20) k).1) * (2 : ℚ) ^ 1024 =
    ∑ i ∈ Finset.range 16,
      ((∑ j ∈ Finset.range 64,
        (ratGammaTerm 240 (1099 / 4000) (3 / 20) (64 * i + j)).1) * (2 : ℚ) ^ 1024)
  have h1024 : 1024 = 64 * 16 := by norm_num
  calc
    _ = (∑ k ∈ Finset.range (64 * 16),
        (ratGammaTerm 240 (1099 / 4000) (3 / 20) k).1) * (2 : ℚ) ^ 1024 := by rw [h1024]
    _ = (∑ i ∈ Finset.range 16, ∑ j ∈ Finset.range 64,
        (ratGammaTerm 240 (1099 / 4000) (3 / 20) (64 * i + j)).1) * (2 : ℚ) ^ 1024 := by
          congr 1
          exact c5GammaComplexNodeUpperSumRangeBlocks
            (fun k => (ratGammaTerm 240 (1099 / 4000) (3 / 20) k).1) 16
    _ = ∑ i ∈ Finset.range 16,
        ((∑ j ∈ Finset.range 64,
          (ratGammaTerm 240 (1099 / 4000) (3 / 20) (64 * i + j)).1) * (2 : ℚ) ^ 1024) := by
          rw [Finset.sum_mul]

theorem c5GammaComplexNodeUpperCoreScaledImag_eq_chunkSum :
    c5GammaComplexNodeUpperCoreScaledImag =
      ∑ i ∈ Finset.range 16, (c5GammaComplexNodeUpperChunk64 i).2 := by
  change
    (∑ k ∈ Finset.range 1024,
      (ratGammaTerm 240 (1099 / 4000) (3 / 20) k).2) * (2 : ℚ) ^ 1024 =
    ∑ i ∈ Finset.range 16,
      ((∑ j ∈ Finset.range 64,
        (ratGammaTerm 240 (1099 / 4000) (3 / 20) (64 * i + j)).2) * (2 : ℚ) ^ 1024)
  have h1024 : 1024 = 64 * 16 := by norm_num
  calc
    _ = (∑ k ∈ Finset.range (64 * 16),
        (ratGammaTerm 240 (1099 / 4000) (3 / 20) k).2) * (2 : ℚ) ^ 1024 := by rw [h1024]
    _ = (∑ i ∈ Finset.range 16, ∑ j ∈ Finset.range 64,
        (ratGammaTerm 240 (1099 / 4000) (3 / 20) (64 * i + j)).2) * (2 : ℚ) ^ 1024 := by
          congr 1
          exact c5GammaComplexNodeUpperSumRangeBlocks
            (fun k => (ratGammaTerm 240 (1099 / 4000) (3 / 20) k).2) 16
    _ = ∑ i ∈ Finset.range 16,
        ((∑ j ∈ Finset.range 64,
          (ratGammaTerm 240 (1099 / 4000) (3 / 20) (64 * i + j)).2) * (2 : ℚ) ^ 1024) := by
          rw [Finset.sum_mul]

theorem c5GammaComplexNodeUpperCoreScaled_chunkBounds :
    (∑ i ∈ Finset.range 16, (c5GammaComplexNodeUpperRealFloor i : ℚ)) ≤
      c5GammaComplexNodeUpperCoreScaledReal ∧
    c5GammaComplexNodeUpperCoreScaledReal <
      ∑ i ∈ Finset.range 16, ((c5GammaComplexNodeUpperRealFloor i : ℚ) + 1) ∧
    (∑ i ∈ Finset.range 16, (c5GammaComplexNodeUpperImagFloor i : ℚ)) ≤
      c5GammaComplexNodeUpperCoreScaledImag ∧
    c5GammaComplexNodeUpperCoreScaledImag <
      ∑ i ∈ Finset.range 16, ((c5GammaComplexNodeUpperImagFloor i : ℚ) + 1) := by
  constructor
  · rw [c5GammaComplexNodeUpperCoreScaledReal_eq_chunkSum]
    apply Finset.sum_le_sum
    intro i hi
    exact_mod_cast Int.floor_le (c5GammaComplexNodeUpperChunk64 i).1
  constructor
  · rw [c5GammaComplexNodeUpperCoreScaledReal_eq_chunkSum]
    apply Finset.sum_lt_sum
    · intro i hi
      exact_mod_cast (Int.lt_floor_add_one (c5GammaComplexNodeUpperChunk64 i).1).le
    · exact ⟨0, by simp, by exact_mod_cast Int.lt_floor_add_one (c5GammaComplexNodeUpperChunk64 0).1⟩
  constructor
  · rw [c5GammaComplexNodeUpperCoreScaledImag_eq_chunkSum]
    apply Finset.sum_le_sum
    intro i hi
    exact_mod_cast Int.floor_le (c5GammaComplexNodeUpperChunk64 i).2
  · rw [c5GammaComplexNodeUpperCoreScaledImag_eq_chunkSum]
    apply Finset.sum_lt_sum
    · intro i hi
      exact_mod_cast (Int.lt_floor_add_one (c5GammaComplexNodeUpperChunk64 i).2).le
    · exact ⟨0, by simp, by exact_mod_cast Int.lt_floor_add_one (c5GammaComplexNodeUpperChunk64 0).2⟩

#print axioms c5GammaComplexNodeUpperCoreScaledReal_eq_chunkSum
#print axioms c5GammaComplexNodeUpperCoreScaledImag_eq_chunkSum
#print axioms c5GammaComplexNodeUpperCoreScaled_chunkBounds

theorem c5GammaComplexNodeUpperRealFloorSum_eq :
    (∑ i ∈ Finset.range 16, (c5GammaComplexNodeUpperRealFloor i : ℚ)) = (24736284287707724345380293922232217822741450645070086431340980213096957504557225152899141696019946041863726969487772749212620094809651825254993717942670154185902848941356303138360062006256842837858824784357000372676512378644034182391062240954696888665411334659595737570860808604307503035900666587786740193437 : ℚ) := by
  norm_num [c5GammaComplexNodeUpperRealFloor,     c5GammaComplexNodeUpperChunk64RealFloor_0,
    c5GammaComplexNodeUpperChunk64RealFloor_1,
    c5GammaComplexNodeUpperChunk64RealFloor_2,
    c5GammaComplexNodeUpperChunk64RealFloor_3,
    c5GammaComplexNodeUpperChunk64RealFloor_4,
    c5GammaComplexNodeUpperChunk64RealFloor_5,
    c5GammaComplexNodeUpperChunk64RealFloor_6,
    c5GammaComplexNodeUpperChunk64RealFloor_7,
    c5GammaComplexNodeUpperChunk64RealFloor_8,
    c5GammaComplexNodeUpperChunk64RealFloor_9,
    c5GammaComplexNodeUpperChunk64RealFloor_10,
    c5GammaComplexNodeUpperChunk64RealFloor_11,
    c5GammaComplexNodeUpperChunk64RealFloor_12,
    c5GammaComplexNodeUpperChunk64RealFloor_13,
    c5GammaComplexNodeUpperChunk64RealFloor_14,
    c5GammaComplexNodeUpperChunk64RealFloor_15, Finset.sum_range_succ]

theorem c5GammaComplexNodeUpperImagFloorSum_eq :
    (∑ i ∈ Finset.range 16, (c5GammaComplexNodeUpperImagFloor i : ℚ)) = (-110647307640131204221990292379858287271369866397943031235381390213779412973499466604613443205284249912893568680981476556928141632345917754956065829322268815882823311250120687666208926404414975969193492673986431780826101825127734354446319158762814120792357760192791986886037073133831239912939515995074618621894 : ℚ) := by
  norm_num [c5GammaComplexNodeUpperImagFloor,     c5GammaComplexNodeUpperChunk64ImagFloor_0,
    c5GammaComplexNodeUpperChunk64ImagFloor_1,
    c5GammaComplexNodeUpperChunk64ImagFloor_2,
    c5GammaComplexNodeUpperChunk64ImagFloor_3,
    c5GammaComplexNodeUpperChunk64ImagFloor_4,
    c5GammaComplexNodeUpperChunk64ImagFloor_5,
    c5GammaComplexNodeUpperChunk64ImagFloor_6,
    c5GammaComplexNodeUpperChunk64ImagFloor_7,
    c5GammaComplexNodeUpperChunk64ImagFloor_8,
    c5GammaComplexNodeUpperChunk64ImagFloor_9,
    c5GammaComplexNodeUpperChunk64ImagFloor_10,
    c5GammaComplexNodeUpperChunk64ImagFloor_11,
    c5GammaComplexNodeUpperChunk64ImagFloor_12,
    c5GammaComplexNodeUpperChunk64ImagFloor_13,
    c5GammaComplexNodeUpperChunk64ImagFloor_14,
    c5GammaComplexNodeUpperChunk64ImagFloor_15, Finset.sum_range_succ]

def c5GammaComplexNodeUpperCoreBox : ZetaLean.ComplexInterval :=
  { re := { lo := (24736284287707724345380293922232217822741450645070086431340980213096957504557225152899141696019946041863726969487772749212620094809651825254993717942670154185902848941356303138360062006256842837858824784357000372676512378644034182391062240954696888665411334659595737570860808604307503035900666587786740193437 : ℚ) / (2 : ℚ) ^ 1024,
            hi := ((24736284287707724345380293922232217822741450645070086431340980213096957504557225152899141696019946041863726969487772749212620094809651825254993717942670154185902848941356303138360062006256842837858824784357000372676512378644034182391062240954696888665411334659595737570860808604307503035900666587786740193437 + 16) : ℚ) / (2 : ℚ) ^ 1024,
            le := by
              have hnum : (24736284287707724345380293922232217822741450645070086431340980213096957504557225152899141696019946041863726969487772749212620094809651825254993717942670154185902848941356303138360062006256842837858824784357000372676512378644034182391062240954696888665411334659595737570860808604307503035900666587786740193437 : ℚ) ≤
                  (24736284287707724345380293922232217822741450645070086431340980213096957504557225152899141696019946041863726969487772749212620094809651825254993717942670154185902848941356303138360062006256842837858824784357000372676512378644034182391062240954696888665411334659595737570860808604307503035900666587786740193437 + 16 : ℚ) := by norm_num
              exact div_le_div_of_nonneg_right hnum (by positivity) },
    im := { lo := (-110647307640131204221990292379858287271369866397943031235381390213779412973499466604613443205284249912893568680981476556928141632345917754956065829322268815882823311250120687666208926404414975969193492673986431780826101825127734354446319158762814120792357760192791986886037073133831239912939515995074618621894 : ℚ) / (2 : ℚ) ^ 1024,
            hi := ((-110647307640131204221990292379858287271369866397943031235381390213779412973499466604613443205284249912893568680981476556928141632345917754956065829322268815882823311250120687666208926404414975969193492673986431780826101825127734354446319158762814120792357760192791986886037073133831239912939515995074618621894 + 16) : ℚ) / (2 : ℚ) ^ 1024,
            le := by
              have hnum : (-110647307640131204221990292379858287271369866397943031235381390213779412973499466604613443205284249912893568680981476556928141632345917754956065829322268815882823311250120687666208926404414975969193492673986431780826101825127734354446319158762814120792357760192791986886037073133831239912939515995074618621894 : ℚ) ≤
                  (-110647307640131204221990292379858287271369866397943031235381390213779412973499466604613443205284249912893568680981476556928141632345917754956065829322268815882823311250120687666208926404414975969193492673986431780826101825127734354446319158762814120792357760192791986886037073133831239912939515995074618621894 + 16 : ℚ) := by norm_num
              exact div_le_div_of_nonneg_right hnum (by positivity) } }

theorem c5GammaComplexNodeUpperCoreBox_contains :
    c5GammaComplexNodeUpperCoreBox.contains (ratComplexToComplex c5GammaComplexNodeUpperCore) := by
  have hbounds := c5GammaComplexNodeUpperCoreScaled_chunkBounds
  have hReLo : (24736284287707724345380293922232217822741450645070086431340980213096957504557225152899141696019946041863726969487772749212620094809651825254993717942670154185902848941356303138360062006256842837858824784357000372676512378644034182391062240954696888665411334659595737570860808604307503035900666587786740193437 : ℚ) ≤ c5GammaComplexNodeUpperCoreScaledReal := by
    simpa [c5GammaComplexNodeUpperRealFloorSum_eq] using hbounds.1
  have hReHi : c5GammaComplexNodeUpperCoreScaledReal < (24736284287707724345380293922232217822741450645070086431340980213096957504557225152899141696019946041863726969487772749212620094809651825254993717942670154185902848941356303138360062006256842837858824784357000372676512378644034182391062240954696888665411334659595737570860808604307503035900666587786740193437 + 16 : ℚ) := by
    calc
      c5GammaComplexNodeUpperCoreScaledReal <
          ∑ i ∈ Finset.range 16, ((c5GammaComplexNodeUpperRealFloor i : ℚ) + 1) := hbounds.2.1
      _ = (24736284287707724345380293922232217822741450645070086431340980213096957504557225152899141696019946041863726969487772749212620094809651825254993717942670154185902848941356303138360062006256842837858824784357000372676512378644034182391062240954696888665411334659595737570860808604307503035900666587786740193437 : ℚ) + 16 := by
        rw [Finset.sum_add_distrib, c5GammaComplexNodeUpperRealFloorSum_eq]
        norm_num
  have hImLo : (-110647307640131204221990292379858287271369866397943031235381390213779412973499466604613443205284249912893568680981476556928141632345917754956065829322268815882823311250120687666208926404414975969193492673986431780826101825127734354446319158762814120792357760192791986886037073133831239912939515995074618621894 : ℚ) ≤ c5GammaComplexNodeUpperCoreScaledImag := by
    simpa [c5GammaComplexNodeUpperImagFloorSum_eq] using hbounds.2.2.1
  have hImHi : c5GammaComplexNodeUpperCoreScaledImag < (-110647307640131204221990292379858287271369866397943031235381390213779412973499466604613443205284249912893568680981476556928141632345917754956065829322268815882823311250120687666208926404414975969193492673986431780826101825127734354446319158762814120792357760192791986886037073133831239912939515995074618621894 + 16 : ℚ) := by
    calc
      c5GammaComplexNodeUpperCoreScaledImag <
          ∑ i ∈ Finset.range 16, ((c5GammaComplexNodeUpperImagFloor i : ℚ) + 1) := hbounds.2.2.2
      _ = (-110647307640131204221990292379858287271369866397943031235381390213779412973499466604613443205284249912893568680981476556928141632345917754956065829322268815882823311250120687666208926404414975969193492673986431780826101825127734354446319158762814120792357760192791986886037073133831239912939515995074618621894 : ℚ) + 16 := by
        rw [Finset.sum_add_distrib, c5GammaComplexNodeUpperImagFloorSum_eq]
        norm_num
  have hden : (0 : ℚ) < (2 : ℚ) ^ 1024 := by positivity
  have hqloRe : (24736284287707724345380293922232217822741450645070086431340980213096957504557225152899141696019946041863726969487772749212620094809651825254993717942670154185902848941356303138360062006256842837858824784357000372676512378644034182391062240954696888665411334659595737570860808604307503035900666587786740193437 : ℚ) / (2 : ℚ) ^ 1024 ≤ c5GammaComplexNodeUpperCore.1 := by
    rw [div_le_iff₀ hden]
    simpa [c5GammaComplexNodeUpperCoreScaledReal] using hReLo
  have hqhiRe : c5GammaComplexNodeUpperCore.1 ≤ (24736284287707724345380293922232217822741450645070086431340980213096957504557225152899141696019946041863726969487772749212620094809651825254993717942670154185902848941356303138360062006256842837858824784357000372676512378644034182391062240954696888665411334659595737570860808604307503035900666587786740193437 + 16 : ℚ) / (2 : ℚ) ^ 1024 := by
    rw [le_div_iff₀ hden]
    have hh : c5GammaComplexNodeUpperCore.1 * (2 : ℚ) ^ 1024 < (24736284287707724345380293922232217822741450645070086431340980213096957504557225152899141696019946041863726969487772749212620094809651825254993717942670154185902848941356303138360062006256842837858824784357000372676512378644034182391062240954696888665411334659595737570860808604307503035900666587786740193437 + 16 : ℚ) := by
      simpa [c5GammaComplexNodeUpperCoreScaledReal] using hReHi
    exact le_of_lt hh
  have hqloIm : (-110647307640131204221990292379858287271369866397943031235381390213779412973499466604613443205284249912893568680981476556928141632345917754956065829322268815882823311250120687666208926404414975969193492673986431780826101825127734354446319158762814120792357760192791986886037073133831239912939515995074618621894 : ℚ) / (2 : ℚ) ^ 1024 ≤ c5GammaComplexNodeUpperCore.2 := by
    rw [div_le_iff₀ hden]
    simpa [c5GammaComplexNodeUpperCoreScaledImag] using hImLo
  have hqhiIm : c5GammaComplexNodeUpperCore.2 ≤ (-110647307640131204221990292379858287271369866397943031235381390213779412973499466604613443205284249912893568680981476556928141632345917754956065829322268815882823311250120687666208926404414975969193492673986431780826101825127734354446319158762814120792357760192791986886037073133831239912939515995074618621894 + 16 : ℚ) / (2 : ℚ) ^ 1024 := by
    rw [le_div_iff₀ hden]
    have hh : c5GammaComplexNodeUpperCore.2 * (2 : ℚ) ^ 1024 < (-110647307640131204221990292379858287271369866397943031235381390213779412973499466604613443205284249912893568680981476556928141632345917754956065829322268815882823311250120687666208926404414975969193492673986431780826101825127734354446319158762814120792357760192791986886037073133831239912939515995074618621894 + 16 : ℚ) := by
      simpa [c5GammaComplexNodeUpperCoreScaledImag] using hImHi
    exact le_of_lt hh
  simp only [ZetaLean.ComplexInterval.contains, ZetaLean.Interval.contains,
    c5GammaComplexNodeUpperCoreBox, ratComplexToComplex]
  constructor
  · constructor
    · exact_mod_cast hqloRe
    · exact_mod_cast hqhiRe
  · constructor
    · exact_mod_cast hqloIm
    · exact_mod_cast hqhiIm

#print axioms c5GammaComplexNodeUpperRealFloorSum_eq
#print axioms c5GammaComplexNodeUpperImagFloorSum_eq
#print axioms c5GammaComplexNodeUpperCoreBox_contains
