import SigmaC5M2TaylorStateCertificate
import Mathlib.Tactic

open CarrySigmaObstruction ZetaLean ZetaLean.ComplexInterval

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def c5M2Stage2PowerReExport : Interval :=
  Interval.mk ((158637937325395919063734807510065503699756799145136186137817462373658999846777730149662094191959954354982073482496341015360383308880981835947149179272783541184353321213832474546405868790199964846078966534481564623076603259190615319764553925612235514082032686600490139 : ℚ) / 528294531135665246352339784916516606518847326036121522127960709026673902556724859474417255887657187894674394993257128678882347559502685537250538978462939576908386683999005084168731517676426441053024232908211188404148028292751561738838396898767036476489538580897737998336)
    ((158637937325395919063734807510065503699756799145136186137817462373658999846777730149662094191959954354982073482496341015360383308880981835947149179272783541184353321213832474546405868790199964846078966534481564623076603259190615319764553925612282890166917052205475629 : ℚ) / 528294531135665246352339784916516606518847326036121522127960709026673902556724859474417255887657187894674394993257128678882347559502685537250538978462939576908386683999005084168731517676426441053024232908211188404148028292751561738838396898767036476489538580897737998336) (by norm_num)

def c5M2Stage2SumReExport : Interval :=
  Interval.mk ((259569942258308565580753376788427073638671789691062911521011586227333261313457533008940812615729743577029604639423127234622476592448134384112262217165688561361087654264232766783933548778955620105089663630615436955114433349377732650724238344398230130519687363101509573383 : ℚ) / 264147265567832623176169892458258303259423663018060761063980354513336951278362429737208627943828593947337197496628564339441173779751342768625269489231469788454193341999502542084365758838213220526512116454105594202074014146375780869419198449383518238244769290448868999168)
    ((519139884516617131161506753576854147277343579382125823042023172454666522626915066017881625231459487154059209278846254469244953184896268768224524434331377122722175308528465533567867097557911240210179327261230873910228866698755465301448476688796461628024229114379773253639 : ℚ) / 528294531135665246352339784916516606518847326036121522127960709026673902556724859474417255887657187894674394993257128678882347559502685537250538978462939576908386683999005084168731517676426441053024232908211188404148028292751561738838396898767036476489538580897737998336) (by norm_num)

def c5M2Stage2 : ComplexInterval × ComplexInterval :=
  (ComplexInterval.mk c5M2Stage2PowerReExport (Interval.exact 0),
    ComplexInterval.mk c5M2Stage2SumReExport (Interval.exact 0))

lemma c5IntervalAddExactZero (x : Interval) :
    x.add (Interval.exact 0) = x := by
  apply c5Interval_ext <;> simp [Interval.add, Interval.exact]

lemma c5IntervalNegExactZero :
    (Interval.exact 0).neg = Interval.exact 0 := by
  apply c5Interval_ext <;> simp [Interval.neg, Interval.exact]

lemma c5IntervalSubExactZero (x : Interval) :
    x.sub (Interval.exact 0) = x := by
  rw [Interval.sub, c5IntervalNegExactZero, c5IntervalAddExactZero]

lemma c5ComplexRealMul (x y : Interval) :
    ({ re := x, im := Interval.exact 0 } : ComplexInterval).mul
      ({ re := y, im := Interval.exact 0 } : ComplexInterval) =
      { re := x.mul y, im := Interval.exact 0 } := by
  apply c5ComplexInterval_ext
  · change (x.mul y).sub ((Interval.exact 0).mul (Interval.exact 0)) = x.mul y
    rw [c5IntervalExactZeroMul, c5IntervalSubExactZero]
  · change (x.mul (Interval.exact 0)).add
      ((Interval.exact 0).mul y) = Interval.exact 0
    rw [c5IntervalMulExactZero, c5IntervalExactZeroMul]
    exact c5IntervalAddExactZero _

lemma c5IntervalMulNonpos (x y : Interval)
    (hx : x.hi ≤ 0) (hy : y.hi ≤ 0) :
    x.mul y = Interval.mk (x.hi * y.hi) (x.lo * y.lo) (by
      have hxlo : x.lo ≤ 0 := le_trans x.le hx
      have h1 : x.lo * y.hi ≤ x.lo * y.lo :=
        mul_le_mul_of_nonpos_left y.le hxlo
      have h3 : x.hi * y.hi ≤ x.lo * y.hi :=
        mul_le_mul_of_nonpos_right x.le hy
      exact le_trans h3 h1) := by
  have hxlo : x.lo ≤ 0 := le_trans x.le hx
  have hylo : y.lo ≤ 0 := le_trans y.le hy
  have h1 : x.lo * y.hi ≤ x.lo * y.lo :=
    mul_le_mul_of_nonpos_left y.le hxlo
  have h2 : x.hi * y.hi ≤ x.hi * y.lo :=
    mul_le_mul_of_nonpos_left y.le hx
  have h3 : x.hi * y.hi ≤ x.lo * y.hi :=
    mul_le_mul_of_nonpos_right x.le hy
  have h4 : x.hi * y.lo ≤ x.lo * y.lo :=
    mul_le_mul_of_nonpos_right x.le hylo
  apply c5Interval_ext
  · change min (min (x.lo * y.lo) (x.lo * y.hi))
      (min (x.hi * y.lo) (x.hi * y.hi)) = x.hi * y.hi
    rw [min_eq_right h1, min_eq_right h2, min_eq_right h3]
  · change max (max (x.lo * y.lo) (x.lo * y.hi))
      (max (x.hi * y.lo) (x.hi * y.hi)) = x.lo * y.lo
    rw [max_eq_left h1, max_eq_left h2, max_eq_left h4]

theorem c5M2Stage2PowerCoarsenExport :
    (c5M2Stage1PowerReExport.mul c5M2TaylorArgExport.re).coarsen 896 =
      c5M2Stage2PowerReExport := by
  have hleft : c5M2Stage1PowerReExport.hi ≤ 0 := by
    change (-9154646619048115190833031339662459241503746653995699085937536572007379929809793456535630656197700740615185714410874209637394374606416769026014544131562454186211375470539550600864420118515200842844905646980314493919161593996096437389920209970574848465309466517964744697 : ℚ) /
      (2 : ℚ) ^ 896 ≤ 0
    exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)
  have hright : c5M2TaylorArgExport.re.hi ≤ 0 := by
    change (-366185864761924607633321253586498369660149866159827963437501462880295197192391738261425226247908029624607428576434968385495774984256670761040581765262498167448455018821582024034576804740608033713796225879212579756766463759843857495596808398822993938612378660718589787915 : ℚ) /
      ((40 : ℚ) * (2 : ℚ) ^ 896) ≤ 0
    exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)
  rw [c5IntervalMulNonpos _ _ hleft hright]
  apply c5Interval_ext
  · norm_num (config := { maxSteps := 1000000 })
      [Interval.coarsen, c5M2Stage1PowerReExport, c5M2TaylorArgExport,
        c5M2Stage2PowerReExport, pow_succ]
  · norm_num (config := { maxSteps := 1000000 })
      [Interval.coarsen, c5M2Stage1PowerReExport, c5M2TaylorArgExport,
        c5M2Stage2PowerReExport, pow_succ]

theorem c5M2Stage2PowerCorrect :
    (c5M2Stage1.1.mul c5M2TaylorArgExport).coarsen 896 = c5M2Stage2.1 := by
  have hm := c5ComplexRealMul c5M2Stage1PowerReExport c5M2TaylorArgExport.re
  change
    (({ re := c5M2Stage1PowerReExport, im := Interval.exact 0 } : ComplexInterval).mul
      ({ re := c5M2TaylorArgExport.re, im := Interval.exact 0 } : ComplexInterval)).coarsen 896 =
      c5M2Stage2.1
  rw [hm]
  apply c5ComplexInterval_ext
  · exact c5M2Stage2PowerCoarsenExport
  · exact c5M2CoarsenZero 896

theorem c5M2Stage2SumCorrect :
    (c5M2Stage1.2.add
      ((ComplexInterval.smulQ (1 / (Nat.factorial 1 : ℚ)) c5M2Stage1.1).coarsen 896)).coarsen 896 =
      c5M2Stage2.2 := by
  have hcoef : (1 / (Nat.factorial 1 : ℚ)) = 1 := by norm_num
  have hscale :
      ComplexInterval.smulQ (1 / (Nat.factorial 1 : ℚ)) c5M2Stage1.1 =
        c5M2Stage1.1 := by
    change (ComplexInterval.exact (1 / (Nat.factorial 1 : ℚ)) 0).mul
      c5M2Stage1.1 = c5M2Stage1.1
    rw [hcoef, c5ComplexExactOneMul]
  rw [hscale]
  apply c5ComplexInterval_ext
  · apply c5Interval_ext
    · norm_num (config := { maxSteps := 1000000 })
        [ComplexInterval.add, ComplexInterval.coarsen,
          c5M2Stage1, c5M2Stage2, c5M2Stage1PowerReExport,
          c5M2Stage2SumReExport, ComplexInterval.exact,
          Interval.add, Interval.coarsen, Interval.exact, pow_succ]
    · norm_num (config := { maxSteps := 1000000 })
        [ComplexInterval.add, ComplexInterval.coarsen,
          c5M2Stage1, c5M2Stage2, c5M2Stage1PowerReExport,
          c5M2Stage2SumReExport, ComplexInterval.exact,
          Interval.add, Interval.coarsen, Interval.exact, pow_succ]
  · apply c5Interval_ext <;>
      norm_num (config := { maxSteps := 1000000 })
        [ComplexInterval.add, ComplexInterval.coarsen,
          c5M2Stage1, c5M2Stage2, c5M2Stage1PowerReExport,
          c5M2Stage2SumReExport, ComplexInterval.exact,
          Interval.add, Interval.coarsen, Interval.exact, pow_succ]

theorem c5RoundedExpStateC_stage2_correct_refined :
    c5RoundedExpStateC 896 c5M2TaylorArgExport 2 = c5M2Stage2 := by
  rw [c5RoundedExpStateC_succ_eq, c5RoundedExpStateC_stage1_correct]
  apply Prod.ext
  · exact c5M2Stage2PowerCorrect
  · exact c5M2Stage2SumCorrect

#print axioms c5M2Stage2PowerCoarsenExport
#print axioms c5M2Stage2PowerCorrect
#print axioms c5M2Stage2SumCorrect
#print axioms c5RoundedExpStateC_stage2_correct_refined
