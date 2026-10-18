import OddSourceTwentyFour

namespace CarrySixthOdd
open CarryIntegralCertificate CarrySelfAdjointOperator CarrySixthEven CarryCriticalSource
open scoped BigOperators
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 48000000

def twelfthCoefficientBox : Box :=
  (((Box.point 2208).mul (thetaInputBox 11)).add thetaTwentyFourBox.neg).div
    (Box.point (4*(Nat.factorial 24:ℤ)))

theorem source_c12_theta : completedNativeRealEvenCharacteristicCoefficient 12 =
    (2208*completedNativeThetaTailMoment 22-completedNativeThetaTailMoment 24)/
      (4*(Nat.factorial 24:ℝ)) := by
  change completedNativeRealEvenCharacteristicCoefficient (11+1) = _
  rw [CarryThetaPattern.sourceCoefficient_theta,CarryThetaPattern.sourceThetaIntegral_moments]
  norm_num

theorem mem_twelfthCoefficientBox :
    twelfthCoefficientBox.Mem (completedNativeRealEvenCharacteristicCoefficient 12) := by
  rw [source_c12_theta]
  have hx := mem_div
    (mem_add (mem_mul (mem_point 2208) (mem_thetaInputBox 11))
      (mem_neg mem_thetaTwentyFourBox)) (mem_point (4*(Nat.factorial 24:ℤ)))
  simpa only [twelfthCoefficientBox,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast,
    Nat.reduceMul,sub_eq_add_neg] using hx

def eleventhMomentBox : Box :=
  (((Box.point (-12)).mul twelfthCoefficientBox).add
    (Box.sum (fun k => (sixthLogMomentBox k).mul (sixthCharacteristicBox (11-k))) 11).neg).div
      (sixthCharacteristicBox 0)

theorem mem_eleventhMomentBox : eleventhMomentBox.Mem (h 11) := by
  have hs := mem_sum _ _ 11 (fun k _ => mem_mul
    (mem_sixthLogMomentBox k) (mem_sixthCharacteristicBox (11-k)))
  have hx := mem_div (mem_add (mem_mul (mem_point (-12)) mem_twelfthCoefficientBox)
    (mem_neg hs)) (mem_sixthCharacteristicBox 0)
  have he := canonicalCompletedNativeLogDerivativeMoment_eq 11
  convert hx using 1
  · rfl
  · change canonicalCompletedNativeLogDerivativeMoment 11 = _
    rw [he]
    norm_num only [Nat.reduceAdd,Nat.cast_ofNat,Int.cast_neg,Int.cast_ofNat]
    ring

def oddSourceMomentBox (n : ℕ) : Box := if n=11 then eleventhMomentBox else sixthLogMomentBox n

theorem mem_oddSourceMomentBox (n : ℕ) : (oddSourceMomentBox n).Mem (h n) := by
  unfold oddSourceMomentBox
  split_ifs with hn
  · subst n; exact mem_eleventhMomentBox
  · exact mem_sixthLogMomentBox n

/-- Computational interval cache, NEVER a new sequence of moments. -/
def compactMomentTable : Fin 12 → Box := ![Box.finite (23104993115418970788580226987208967357482399299175557015170) (23104993115418970789349209283074309292782627219045464890720),
  Box.finite (37172599285269686108016343697831913114243072182268108981) (37172599285269686228561299079518106474846587656098807264),
  Box.finite (144173931400973275188546686199315265059731903576722587) (144173931400973284343411971929598360720637169944104726),
  Box.finite (663031680252990658486662165446309489090944692400541) (663031680252991082998309105319780319694895514408012),
  Box.finite (3213664150616593564497465475107701729429669031087) (3213664150616608883629048292458715070561753829545),
  Box.finite (15876934514909899275924558069713347161308095137) (15876934514910407884863680966850910472850390886),
  Box.finite (79033257240459079462599076986646028493886044) (79033257240475679574529342482489620224773327),
  Box.finite (394647139999614252978148270534781671242233) (394647140000154978991171825227913529338366),
  Box.finite (1973265073736161656573770931897238508895) (1973265073753772926631405414036276716683),
  Box.finite (9872165383010363365054717395972531189) (9872165383583951996724468152456518606),
  Box.finite (49402563513479088563014529525131110) (49402563532160493356254039466083928),
  Box.finite (247249444128656506295618364927720) (247249444737097368259026748858694)]

def compactMomentBox (n : ℕ) : Box := if h : n < 12 then compactMomentTable ⟨n,h⟩ else .all

theorem compact_moment_checks : ∀ j : Fin 12,
    (oddSourceMomentBox j.val).contained (compactMomentBox j.val) = true := by
  decide +kernel

theorem mem_compactMomentBox (n : ℕ) : (compactMomentBox n).Mem (h n) := by
  by_cases hn : n < 12
  · exact mem_of_contained (mem_oddSourceMomentBox n) (compact_moment_checks ⟨n,hn⟩)
  · simp only [compactMomentBox,dif_neg hn,Box.Mem]

end CarrySixthOdd
