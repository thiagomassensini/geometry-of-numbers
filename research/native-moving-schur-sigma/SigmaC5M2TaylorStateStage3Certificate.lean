import SigmaC5M2TaylorStateStage2Refined
import Mathlib.Tactic

open CarrySigmaObstruction ZetaLean ZetaLean.ComplexInterval

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def c5M2Stage3PowerReExport : Interval :=
  Interval.mk ((-2748985974673587314587907916873772378901943400803970312523723629692653177229679569685706617781680733591558054273793260726589144493825702637771521724241016465325615306122974293058214458122814981387732402616954637236951828788048911992562620204976469190564797649902973 : ℚ) / 528294531135665246352339784916516606518847326036121522127960709026673902556724859474417255887657187894674394993257128678882347559502685537250538978462939576908386683999005084168731517676426441053024232908211188404148028292751561738838396898767036476489538580897737998336) ((-1374492987336793657293953958436886189450971700401985156261861814846326588614839784842853308890840366795779027136896630363294572246912851318885760862120508232662807653061487146529107229061407490693866201308477318618475914394024455996281310102487618871538706950044719 : ℚ) / 264147265567832623176169892458258303259423663018060761063980354513336951278362429737208627943828593947337197496628564339441173779751342768625269489231469788454193341999502542084365758838213220526512116454105594202074014146375780869419198449383518238244769290448868999168) (by norm_num)

def c5M2Stage3TermReExport : Interval :=
  Interval.mk ((79318968662697959531867403755032751849878399572568093068908731186829499923388865074831047095979977177491036741248170507680191654440490917973574589636391770592176660606916237273202934395099982423039483267240782311538301629595307659882276962806117757041016343300245069 : ℚ) / 528294531135665246352339784916516606518847326036121522127960709026673902556724859474417255887657187894674394993257128678882347559502685537250538978462939576908386683999005084168731517676426441053024232908211188404148028292751561738838396898767036476489538580897737998336) ((79318968662697959531867403755032751849878399572568093068908731186829499923388865074831047095979977177491036741248170507680191654440490917973574589636391770592176660606916237273202934395099982423039483267240782311538301629595307659882276962806141445083458526102737815 : ℚ) / 528294531135665246352339784916516606518847326036121522127960709026673902556724859474417255887657187894674394993257128678882347559502685537250538978462939576908386683999005084168731517676426441053024232908211188404148028292751561738838396898767036476489538580897737998336) (by norm_num)

def c5M2Stage3SumReExport : Interval :=
  Interval.mk ((519219203485279829121038620980609180029193457781698391135092081185853352126838454882956456278555467131236700315587502639752633376550709259142498008921013514492767485189072449805140300492306340192602366744498114692540405000385060609108358965759266378796415742546319391835 : ℚ) / 528294531135665246352339784916516606518847326036121522127960709026673902556724859474417255887657187894674394993257128678882347559502685537250538978462939576908386683999005084168731517676426441053024232908211188404148028292751561738838396898767036476489538580897737998336) ((259609601742639914560519310490304590014596728890849195567546040592926676063419227441478228139277733565618350157793751319876316688275354629571249004460506757246383742594536224902570150246153170096301183372249057346270202500192530304554179482879633884734656286452937995727 : ℚ) / 264147265567832623176169892458258303259423663018060761063980354513336951278362429737208627943828593947337197496628564339441173779751342768625269489231469788454193341999502542084365758838213220526512116454105594202074014146375780869419198449383518238244769290448868999168) (by norm_num)


def c5M2Stage3 : ComplexInterval × ComplexInterval :=
  (ComplexInterval.mk c5M2Stage3PowerReExport (Interval.exact 0),
    ComplexInterval.mk c5M2Stage3SumReExport (Interval.exact 0))

lemma c5IntervalMulNonnegNonpos (x y : Interval)
    (hx : 0 ≤ x.lo) (hy : y.hi ≤ 0) :
    x.mul y = Interval.mk (x.hi * y.lo) (x.lo * y.hi) (by
      have h1 : x.lo * y.lo ≤ x.lo * y.hi :=
        mul_le_mul_of_nonneg_left y.le hx
      have h2 : x.hi * y.lo ≤ x.lo * y.lo :=
        mul_le_mul_of_nonpos_right x.le (le_trans y.le hy)
      exact le_trans h2 h1) := by
  have hxhi : 0 ≤ x.hi := le_trans hx x.le
  have h1 : x.lo * y.lo ≤ x.lo * y.hi :=
    mul_le_mul_of_nonneg_left y.le hx
  have h2 : x.hi * y.lo ≤ x.lo * y.lo :=
    mul_le_mul_of_nonpos_right x.le (le_trans y.le hy)
  have h3 : x.hi * y.lo ≤ x.hi * y.hi :=
    mul_le_mul_of_nonneg_left y.le hxhi
  have h4 : x.hi * y.hi ≤ x.lo * y.hi :=
    mul_le_mul_of_nonpos_right x.le hy
  apply c5Interval_ext
  · change min (min (x.lo * y.lo) (x.lo * y.hi))
      (min (x.hi * y.lo) (x.hi * y.hi)) = x.hi * y.lo
    rw [min_eq_left h1, min_eq_left h3, min_eq_right h2]
  · change max (max (x.lo * y.lo) (x.lo * y.hi))
      (max (x.hi * y.lo) (x.hi * y.hi)) = x.lo * y.hi
    rw [max_eq_right h1, max_eq_right h3, max_eq_left h4]

lemma c5IntervalExactNonnegMul (q : ℚ) (hq : 0 ≤ q) (x : Interval) :
    (Interval.exact q).mul x =
      Interval.mk (q * x.lo) (q * x.hi) (mul_le_mul_of_nonneg_left x.le hq) := by
  have h : q * x.lo ≤ q * x.hi := mul_le_mul_of_nonneg_left x.le hq
  apply c5Interval_ext
  · change min (min (q * x.lo) (q * x.hi))
      (min (q * x.lo) (q * x.hi)) = q * x.lo
    rw [min_eq_left h, min_self]
  · change max (max (q * x.lo) (q * x.hi))
      (max (q * x.lo) (q * x.hi)) = q * x.hi
    rw [max_eq_right h, max_self]

theorem c5M2Stage3PowerCoarsenExport :
    (c5M2Stage2PowerReExport.mul c5M2TaylorArgExport.re).coarsen 896 =
      c5M2Stage3PowerReExport := by
  have hleft : 0 ≤ c5M2Stage2PowerReExport.lo := by
    change 0 ≤ ((158637937325395919063734807510065503699756799145136186137817462373658999846777730149662094191959954354982073482496341015360383308880981835947149179272783541184353321213832474546405868790199964846078966534481564623076603259190615319764553925612235514082032686600490139 : ℚ) /
      528294531135665246352339784916516606518847326036121522127960709026673902556724859474417255887657187894674394993257128678882347559502685537250538978462939576908386683999005084168731517676426441053024232908211188404148028292751561738838396898767036476489538580897737998336)
    exact div_nonneg (by norm_num) (by positivity)
  have hright : c5M2TaylorArgExport.re.hi ≤ 0 := by
    change (-366185864761924607633321253586498369660149866159827963437501462880295197192391738261425226247908029624607428576434968385495774984256670761040581765262498167448455018821582024034576804740608033713796225879212579756766463759843857495596808398822993938612378660718589787915 : ℚ) /
      ((40 : ℚ) * (2 : ℚ) ^ 896) ≤ 0
    exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)
  rw [c5IntervalMulNonnegNonpos _ _ hleft hright]
  apply c5Interval_ext
  · norm_num (config := { maxSteps := 1000000 })
      [Interval.coarsen, c5M2Stage2PowerReExport, c5M2TaylorArgExport,
        c5M2Stage3PowerReExport, pow_succ]
  · norm_num (config := { maxSteps := 1000000 })
      [Interval.coarsen, c5M2Stage2PowerReExport, c5M2TaylorArgExport,
        c5M2Stage3PowerReExport, pow_succ]

theorem c5M2Stage3PowerCorrect :
    (c5M2Stage2.1.mul c5M2TaylorArgExport).coarsen 896 = c5M2Stage3.1 := by
  have hm := c5ComplexRealMul c5M2Stage2PowerReExport c5M2TaylorArgExport.re
  change
    (({ re := c5M2Stage2PowerReExport, im := Interval.exact 0 } : ComplexInterval).mul
      ({ re := c5M2TaylorArgExport.re, im := Interval.exact 0 } : ComplexInterval)).coarsen 896 =
      c5M2Stage3.1
  rw [hm]
  apply c5ComplexInterval_ext
  · exact c5M2Stage3PowerCoarsenExport
  · exact c5M2CoarsenZero 896

theorem c5M2Stage3TermCoarsenExport :
    (ComplexInterval.smulQ (1 / 2) c5M2Stage2.1).coarsen 896 =
      ComplexInterval.mk c5M2Stage3TermReExport (Interval.exact 0) := by
  have hm := c5ComplexRealMul (Interval.exact (1 / 2)) c5M2Stage2PowerReExport
  have hscale :
      ComplexInterval.smulQ (1 / 2) c5M2Stage2.1 =
        { re := (Interval.exact (1 / 2)).mul c5M2Stage2PowerReExport,
          im := Interval.exact 0 } := by
    change ({ re := Interval.exact (1 / 2), im := Interval.exact 0 } : ComplexInterval).mul
      ({ re := c5M2Stage2PowerReExport, im := Interval.exact 0 } : ComplexInterval) = _
    exact hm
  rw [hscale, c5IntervalExactNonnegMul (1 / 2) (by norm_num)]
  apply c5ComplexInterval_ext
  · apply c5Interval_ext <;>
      norm_num (config := { maxSteps := 1000000 })
        [ComplexInterval.coarsen, c5M2Stage2PowerReExport,
          c5M2Stage3TermReExport, Interval.coarsen, pow_succ]
  · exact c5M2CoarsenZero 896

theorem c5M2Stage3SumCorrect :
    (c5M2Stage2.2.add
      ((ComplexInterval.smulQ (1 / (Nat.factorial 2 : ℚ)) c5M2Stage2.1).coarsen 896)).coarsen 896 =
      c5M2Stage3.2 := by
  have hcoef : (1 / (Nat.factorial 2 : ℚ)) = 1 / 2 := by norm_num
  rw [hcoef, c5M2Stage3TermCoarsenExport]
  apply c5ComplexInterval_ext
  · apply c5Interval_ext <;>
      norm_num (config := { maxSteps := 1000000 })
        [ComplexInterval.add, ComplexInterval.coarsen,
          c5M2Stage2, c5M2Stage2SumReExport, c5M2Stage3,
          c5M2Stage3SumReExport, c5M2Stage3TermReExport,
          Interval.add, Interval.coarsen, Interval.exact, pow_succ]
  · apply c5Interval_ext <;>
      norm_num (config := { maxSteps := 1000000 })
        [ComplexInterval.add, ComplexInterval.coarsen,
          c5M2Stage2, c5M2Stage2SumReExport, c5M2Stage3,
          c5M2Stage3SumReExport, c5M2Stage3TermReExport,
          Interval.add, Interval.coarsen, Interval.exact, pow_succ]

theorem c5RoundedExpStateC_stage3_correct :
    c5RoundedExpStateC 896 c5M2TaylorArgExport 3 = c5M2Stage3 := by
  rw [c5RoundedExpStateC_succ_eq, c5RoundedExpStateC_stage2_correct_refined]
  apply Prod.ext
  · exact c5M2Stage3PowerCorrect
  · exact c5M2Stage3SumCorrect

#print axioms c5M2Stage3PowerCoarsenExport
#print axioms c5M2Stage3PowerCorrect
#print axioms c5M2Stage3TermCoarsenExport
#print axioms c5M2Stage3SumCorrect
#print axioms c5RoundedExpStateC_stage3_correct
