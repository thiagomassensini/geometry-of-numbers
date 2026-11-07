import SigmaC5M2LogCoarsenCertificate
import Mathlib.Tactic
open CarrySigmaObstruction ZetaLean ZetaLean.ComplexInterval
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem c5Interval_exact_neg_mul (c : ℚ) (hc : 0 ≤ c) (x : Interval) :
    (Interval.exact (-c)).mul x =
      Interval.mk ((-c) * x.hi) ((-c) * x.lo) (by nlinarith [x.le]) := by
  apply c5Interval_ext
  · have hmul : (-c) * x.hi ≤ (-c) * x.lo :=
      mul_le_mul_of_nonpos_left x.le (by linarith)
    simp only [Interval.mul, Interval.exact]
    simp only [min_self]
    exact min_eq_right hmul
  · have hmul : (-c) * x.hi ≤ (-c) * x.lo :=
      mul_le_mul_of_nonpos_left x.le (by linarith)
    simp only [Interval.mul, Interval.exact]
    simp only [max_self]
    exact max_eq_left hmul

theorem c5ComplexInterval_ext {x y : ComplexInterval}
    (hre : x.re = y.re) (him : x.im = y.im) : x = y := by
  cases x
  cases y
  simp_all

def c5M2ExpArgExpr : ComplexInterval :=
  (ComplexInterval.exact (2 / 5) 0).neg.mul
    { re := c5M2LogTwoCoarsenExport,
      im := Interval.exact 0 }

def c5M2TaylorArgExpr : ComplexInterval :=
  ComplexInterval.halveC
    (ComplexInterval.halveC
      (ComplexInterval.halveC
        (ComplexInterval.halveC c5M2ExpArgExpr)))

def c5M2TaylorArgExport : ComplexInterval :=
  ComplexInterval.mk
    (Interval.mk ((-366185864761924607633321253586498369660149866159827963437501462880295197192391738261425226247908029624607428576434968385495774984256670761040581765262498167448455018821582024034576804740608033713796225879212579756766463759843857495596808398823048618006554187788754062763 : ℚ) / ((40 : ℚ) * (2 : ℚ) ^ 896))
      ((-366185864761924607633321253586498369660149866159827963437501462880295197192391738261425226247908029624607428576434968385495774984256670761040581765262498167448455018821582024034576804740608033713796225879212579756766463759843857495596808398822993938612378660718589787915 : ℚ) / ((40 : ℚ) * (2 : ℚ) ^ 896)) (by
      have hn : (-366185864761924607633321253586498369660149866159827963437501462880295197192391738261425226247908029624607428576434968385495774984256670761040581765262498167448455018821582024034576804740608033713796225879212579756766463759843857495596808398823048618006554187788754062763 : ℚ) ≤ -366185864761924607633321253586498369660149866159827963437501462880295197192391738261425226247908029624607428576434968385495774984256670761040581765262498167448455018821582024034576804740608033713796225879212579756766463759843857495596808398822993938612378660718589787915 := by norm_num
      exact div_le_div_of_nonneg_right hn (by norm_num)))
    (Interval.exact 0)

theorem c5M2ExpArgExpr_eq_simple :
    c5M2ExpArgExpr =
      { re := Interval.mk ((- (2 / 5 : ℚ)) * c5M2LogTwoCoarsenExport.hi)
          ((- (2 / 5 : ℚ)) * c5M2LogTwoCoarsenExport.lo) (by nlinarith [c5M2LogTwoCoarsenExport.le]),
        im := Interval.exact 0 } := by
  have hmul :
      (Interval.exact (-(2 / 5 : ℚ))).mul c5M2LogTwoCoarsenExport =
        Interval.mk ((-(2 / 5 : ℚ)) * c5M2LogTwoCoarsenExport.hi)
          ((-(2 / 5 : ℚ)) * c5M2LogTwoCoarsenExport.lo)
          (by nlinarith [c5M2LogTwoCoarsenExport.le]) :=
    c5Interval_exact_neg_mul (2 / 5) (by norm_num) c5M2LogTwoCoarsenExport
  rw [show c5M2ExpArgExpr =
      { re := (Interval.exact (-(2 / 5 : ℚ))).mul c5M2LogTwoCoarsenExport,
        im := Interval.exact 0 } by
        simp [c5M2ExpArgExpr, ComplexInterval.exact, ComplexInterval.neg,
          ComplexInterval.mul, Interval.exact, Interval.neg, Interval.sub,
          Interval.add, Interval.mul]]
  rw [hmul]

theorem c5M2TaylorArgExpr_eq_export :
    c5M2TaylorArgExpr = c5M2TaylorArgExport := by
  unfold c5M2TaylorArgExpr
  rw [c5M2ExpArgExpr_eq_simple]
  apply c5ComplexInterval_ext
  · apply c5Interval_ext
    · norm_num (config := { maxSteps := 1000000 })
        [pow_succ, c5M2TaylorArgExport, c5M2LogTwoCoarsenExport,
         ComplexInterval.halveC, Interval.halve]
    · norm_num (config := { maxSteps := 1000000 })
        [pow_succ, c5M2TaylorArgExport, c5M2LogTwoCoarsenExport,
         ComplexInterval.halveC, Interval.halve]
  · simp [c5M2TaylorArgExport, ComplexInterval.halveC,
      Interval.halve, Interval.exact]

#print axioms c5Interval_exact_neg_mul
#print axioms c5M2ExpArgExpr_eq_simple
#print axioms c5M2TaylorArgExpr_eq_export
