import SigmaC5M2TaylorArgCertificate
import Mathlib.Tactic
open CarrySigmaObstruction ZetaLean ZetaLean.ComplexInterval
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

lemma c5IntervalExactOneMul (x : Interval) :
    (Interval.exact 1).mul x = x := by
  apply c5Interval_ext
  · simp only [Interval.mul, Interval.exact, one_mul, min_self]
    exact min_eq_left x.le
  · simp only [Interval.mul, Interval.exact, one_mul, max_self]
    exact max_eq_right x.le

lemma c5IntervalMulExactOne (x : Interval) :
    x.mul (Interval.exact 1) = x := by
  apply c5Interval_ext
  · simp only [Interval.mul, Interval.exact, mul_one, min_self]
    exact min_eq_left x.le
  · simp only [Interval.mul, Interval.exact, mul_one, max_self]
    exact max_eq_right x.le

lemma c5IntervalExactZeroMul (x : Interval) :
    (Interval.exact 0).mul x = Interval.exact 0 := by
  apply c5Interval_ext <;> simp [Interval.mul, Interval.exact]

lemma c5IntervalMulExactZero (x : Interval) :
    x.mul (Interval.exact 0) = Interval.exact 0 := by
  apply c5Interval_ext <;> simp [Interval.mul, Interval.exact]

lemma c5ComplexExactOneMul (x : ComplexInterval) :
    (ComplexInterval.exact 1 0).mul x = x := by
  apply c5ComplexInterval_ext
  · simp only [ComplexInterval.mul, ComplexInterval.exact]
    rw [c5IntervalExactOneMul, c5IntervalExactZeroMul]
    simp [Interval.sub, Interval.add, Interval.neg, Interval.exact]
  · simp only [ComplexInterval.mul, ComplexInterval.exact]
    rw [c5IntervalExactOneMul, c5IntervalExactZeroMul]
    simp [Interval.add, Interval.exact]

lemma c5M2CoarsenZero (p : ℕ) :
    (Interval.exact 0).coarsen p = Interval.exact 0 := by
  simp [Interval.coarsen, Interval.exact]

lemma c5M2CoarsenOne (p : ℕ) :
    (Interval.exact 1).coarsen p = Interval.exact 1 := by
  apply c5Interval_ext
  · change ((Int.floor ((1 : ℚ) * 2 ^ p) : ℤ) : ℚ) / 2 ^ p = 1
    have hp : (2 : ℚ) ^ p = ((2 ^ p : ℕ) : ℚ) := by norm_cast
    rw [one_mul, hp, Int.floor_natCast]
    norm_num
  · change ((Int.ceil ((1 : ℚ) * 2 ^ p) : ℤ) : ℚ) / 2 ^ p = 1
    have hp : (2 : ℚ) ^ p = ((2 ^ p : ℕ) : ℚ) := by norm_cast
    rw [one_mul, hp, Int.ceil_natCast]
    norm_num

lemma c5ComplexExactOneCoarsen (p : ℕ) :
    (ComplexInterval.exact 1 0).coarsen p = ComplexInterval.exact 1 0 := by
  apply c5ComplexInterval_ext
  · exact c5M2CoarsenOne p
  · exact c5M2CoarsenZero p

lemma c5M2ExactZeroAddOne :
    (ComplexInterval.exact 0 0).add (ComplexInterval.exact 1 0) =
      ComplexInterval.exact 1 0 := by
  apply c5ComplexInterval_ext
  · apply c5Interval_ext <;>
      norm_num [ComplexInterval.add, ComplexInterval.exact,
        Interval.add, Interval.exact]
  · apply c5Interval_ext <;>
      norm_num [ComplexInterval.add, ComplexInterval.exact,
        Interval.add, Interval.exact]

lemma c5M2Stage1TaylorTerm :
    (ComplexInterval.smulQ (1 / (Nat.factorial 0 : ℚ))
      (ComplexInterval.exact 1 0)).coarsen 896 = ComplexInterval.exact 1 0 := by
  have hcoef : (1 / (Nat.factorial 0 : ℚ)) = 1 := by norm_num
  change ((ComplexInterval.exact (1 / (Nat.factorial 0 : ℚ)) 0).mul
    (ComplexInterval.exact 1 0)).coarsen 896 = ComplexInterval.exact 1 0
  rw [hcoef, c5ComplexExactOneMul]
  exact c5ComplexExactOneCoarsen 896

lemma c5RoundedExpStateC_succ_eq (p n : ℕ) (x : ComplexInterval) :
    c5RoundedExpStateC p x (n + 1) =
      (((c5RoundedExpStateC p x n).1.mul x).coarsen p,
        ((c5RoundedExpStateC p x n).2.add
          ((ComplexInterval.smulQ (1 / n.factorial) (c5RoundedExpStateC p x n).1).coarsen p)).coarsen p) := by
  rfl

def c5M2Stage0 : ComplexInterval × ComplexInterval :=
  (ComplexInterval.exact 1 0, ComplexInterval.exact 0 0)

def c5M2Stage1PowerReExport : Interval :=
  Interval.mk ((-9154646619048115190833031339662459241503746653995699085937536572007379929809793456535630656197700740615185714410874209637394374606416769026014544131562454186211375470539550600864420118515200842844905646980314493919161593996096437389920209970576215450163854694718851570 : ℚ) / (2 : ℚ) ^ 896) ((-9154646619048115190833031339662459241503746653995699085937536572007379929809793456535630656197700740615185714410874209637394374606416769026014544131562454186211375470539550600864420118515200842844905646980314493919161593996096437389920209970574848465309466517964744697 : ℚ) / (2 : ℚ) ^ 896) (by
      have hn : (-9154646619048115190833031339662459241503746653995699085937536572007379929809793456535630656197700740615185714410874209637394374606416769026014544131562454186211375470539550600864420118515200842844905646980314493919161593996096437389920209970576215450163854694718851570 : ℚ) ≤ -9154646619048115190833031339662459241503746653995699085937536572007379929809793456535630656197700740615185714410874209637394374606416769026014544131562454186211375470539550600864420118515200842844905646980314493919161593996096437389920209970574848465309466517964744697 := by norm_num
      exact div_le_div_of_nonneg_right hn (by norm_num))

def c5M2Stage1 : ComplexInterval × ComplexInterval :=
  (ComplexInterval.mk c5M2Stage1PowerReExport (Interval.exact 0),
    ComplexInterval.exact 1 0)

theorem c5M2TaylorArgExport_coarsen_re_eq :
    c5M2TaylorArgExport.re.coarsen 896 = c5M2Stage1PowerReExport := by
  apply c5Interval_ext
  · change ((Int.floor (c5M2TaylorArgExport.re.lo * (2 : ℚ) ^ 896) : ℤ) : ℚ) /
      (2 : ℚ) ^ 896 = c5M2Stage1PowerReExport.lo
    have hf : Int.floor (c5M2TaylorArgExport.re.lo * (2 : ℚ) ^ 896) =
        -9154646619048115190833031339662459241503746653995699085937536572007379929809793456535630656197700740615185714410874209637394374606416769026014544131562454186211375470539550600864420118515200842844905646980314493919161593996096437389920209970576215450163854694718851570 := by
      change Int.floor (((-366185864761924607633321253586498369660149866159827963437501462880295197192391738261425226247908029624607428576434968385495774984256670761040581765262498167448455018821582024034576804740608033713796225879212579756766463759843857495596808398823048618006554187788754062763 : ℚ) / ((40 : ℚ) * (2 : ℚ) ^ 896)) * (2 : ℚ) ^ 896) = _
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num (config := { maxSteps := 1000000 }) [pow_succ]
    rw [hf]
    norm_num [c5M2Stage1PowerReExport, pow_succ]
  · change ((Int.ceil (c5M2TaylorArgExport.re.hi * (2 : ℚ) ^ 896) : ℤ) : ℚ) /
      (2 : ℚ) ^ 896 = c5M2Stage1PowerReExport.hi
    have hc : Int.ceil (c5M2TaylorArgExport.re.hi * (2 : ℚ) ^ 896) =
        -9154646619048115190833031339662459241503746653995699085937536572007379929809793456535630656197700740615185714410874209637394374606416769026014544131562454186211375470539550600864420118515200842844905646980314493919161593996096437389920209970574848465309466517964744697 := by
      change Int.ceil (((-366185864761924607633321253586498369660149866159827963437501462880295197192391738261425226247908029624607428576434968385495774984256670761040581765262498167448455018821582024034576804740608033713796225879212579756766463759843857495596808398822993938612378660718589787915 : ℚ) / ((40 : ℚ) * (2 : ℚ) ^ 896)) * (2 : ℚ) ^ 896) = _
      apply Int.ceil_eq_iff.mpr
      constructor <;> norm_num (config := { maxSteps := 1000000 }) [pow_succ]
    rw [hc]
    norm_num [c5M2Stage1PowerReExport, pow_succ]

theorem c5M2TaylorArgExport_coarsen_eq :
    c5M2TaylorArgExport.coarsen 896 = c5M2Stage1.1 := by
  apply c5ComplexInterval_ext
  · exact c5M2TaylorArgExport_coarsen_re_eq
  · change (Interval.exact 0).coarsen 896 = Interval.exact 0
    exact c5M2CoarsenZero 896

theorem c5RoundedExpStateC_stage0_correct :
    c5RoundedExpStateC 896 c5M2TaylorArgExport 0 = c5M2Stage0 := by
  rfl

theorem c5RoundedExpStateC_stage1_correct :
    c5RoundedExpStateC 896 c5M2TaylorArgExport 1 = c5M2Stage1 := by
  rw [c5RoundedExpStateC_succ_eq, c5RoundedExpStateC_stage0_correct]
  simp only [c5M2Stage0]
  rw [c5ComplexExactOneMul]
  apply Prod.ext
  · exact c5M2TaylorArgExport_coarsen_eq
  · change ((ComplexInterval.exact 0 0).add
      ((ComplexInterval.smulQ (1 / (Nat.factorial 0 : ℚ))
        (ComplexInterval.exact 1 0)).coarsen 896)).coarsen 896 =
        ComplexInterval.exact 1 0
    rw [c5M2Stage1TaylorTerm, c5M2ExactZeroAddOne]
    exact c5ComplexExactOneCoarsen 896

#print axioms c5M2TaylorArgExport_coarsen_re_eq
#print axioms c5M2TaylorArgExport_coarsen_eq
#print axioms c5M2Stage1TaylorTerm
#print axioms c5RoundedExpStateC_stage1_correct
