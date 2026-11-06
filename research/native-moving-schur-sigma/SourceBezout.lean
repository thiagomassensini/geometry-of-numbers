module
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Tactic

@[expose] public section
/-! Source-only Bezout kernels, with independent formal arguments.
No physical vector, metric or moment sequence is defined by this construction.
The congruence is algebraic and does not assert positivity. -/
namespace CarrySourceBezout
open scoped BigOperators
noncomputable section
variable {R : Type*} [CommRing R] [IsDomain R]

abbrev BiSeries (R : Type*) [CommRing R] := PowerSeries (PowerSeries R)

def left : PowerSeries R →+* BiSeries R := PowerSeries.map PowerSeries.C
def right : PowerSeries R →+* BiSeries R := PowerSeries.C

def divided (f : PowerSeries R) : BiSeries R :=
  PowerSeries.mk fun i => PowerSeries.mk fun j => PowerSeries.coeff (i+j+1) f

def uv : BiSeries R := PowerSeries.X - PowerSeries.C PowerSeries.X

omit [IsDomain R] in
theorem divided_identity (f : PowerSeries R) :
    uv * divided f = left f - right f := by
  have hm : PowerSeries.constantCoeff ((PowerSeries.map PowerSeries.C) f) =
      PowerSeries.C (PowerSeries.constantCoeff f) := rfl
  apply PowerSeries.ext
  intro i
  apply PowerSeries.ext
  intro j
  cases i <;> cases j <;>
    simp [uv, divided, left, right, sub_mul, PowerSeries.coeff_succ_X_mul,
      hm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem uv_ne_zero : (uv : BiSeries R) ≠ 0 := by
  intro h
  have e := congrArg (fun f : BiSeries R =>
    PowerSeries.coeff 0 (PowerSeries.coeff 1 f)) h
  simp [uv] at e

/-- Defined only from the two original complete source traces. -/
def bezout (a c : PowerSeries R) : BiSeries R :=
  right c * divided a - right a * divided c

omit [IsDomain R] in
theorem bezout_numerator (a c : PowerSeries R) :
    uv * bezout a c = left a * right c - right a * left c := by
  calc
    uv * bezout a c = right c * (uv * divided a) -
        right a * (uv * divided c) := by unfold bezout; ring
    _ = left a * right c - right a * left c := by
      rw [divided_identity, divided_identity]
      ring

/-- The factorization follows from source multiplication, not a fitted Gram. -/
theorem bezout_product (c f : PowerSeries R) :
    bezout (c*f) c = left c * right c * divided f := by
  apply mul_left_cancel₀ uv_ne_zero
  rw [bezout_numerator]
  rw [map_mul, map_mul]
  calc
    left c * left f * right c - right c * right f * left c =
        left c * right c * (left f - right f) := by ring
    _ = uv * (left c * right c * divided f) := by rw [← divided_identity]; ring

def momentSeries (h : ℕ → R) : PowerSeries R := PowerSeries.mk h

def sourceSeries (c : ℕ → R) : PowerSeries R := PowerSeries.mk c

def hankelSeries (h : ℕ → R) (s : ℕ) : BiSeries R :=
  PowerSeries.mk fun i => PowerSeries.mk fun j => h (i+j+s)

def sourceKernel (c : ℕ → R) (oddSector : Bool) : BiSeries R :=
  let C := sourceSeries c
  let A := -(PowerSeries.derivative R C)
  bezout (if oddSector then A else PowerSeries.X * A) C

/-- One convolution equation, with no assumption about signs or invertibility. -/
def SourceRecurrence (c h : ℕ → R) : Prop :=
  sourceSeries c * momentSeries h = -(PowerSeries.derivative R (sourceSeries c))

omit [IsDomain R] in
theorem source_kernel_numerator_even (c : ℕ → R) :
    uv * sourceKernel c false =
      right (PowerSeries.X * PowerSeries.derivative R (sourceSeries c)) * left (sourceSeries c) -
      left (PowerSeries.X * PowerSeries.derivative R (sourceSeries c)) * right (sourceSeries c) := by
  change uv * bezout (PowerSeries.X * -(PowerSeries.derivative R (sourceSeries c)))
    (sourceSeries c) = _
  rw [bezout_numerator]
  simp only [map_mul, map_neg]
  ring

omit [IsDomain R] in
theorem source_kernel_numerator_odd (c : ℕ → R) :
    uv * sourceKernel c true =
      right (PowerSeries.derivative R (sourceSeries c)) * left (sourceSeries c) -
      left (PowerSeries.derivative R (sourceSeries c)) * right (sourceSeries c) := by
  change uv * bezout (-(PowerSeries.derivative R (sourceSeries c))) (sourceSeries c) = _
  rw [bezout_numerator]
  simp only [map_neg]
  ring

theorem source_kernel_even (c h : ℕ → R) (hc : SourceRecurrence c h) :
    sourceKernel c false = left (sourceSeries c) * right (sourceSeries c) *
      hankelSeries h 0 := by
  have hA : PowerSeries.X * -(PowerSeries.derivative R (sourceSeries c)) =
      sourceSeries c * (PowerSeries.X * momentSeries h) := by rw [← hc]; ring
  simp only [sourceKernel, Bool.false_eq_true, ↓reduceIte, hA, bezout_product]
  congr 1
  apply PowerSeries.ext
  intro i
  apply PowerSeries.ext
  intro j
  simp [divided, hankelSeries, momentSeries, PowerSeries.coeff_succ_X_mul]

theorem source_kernel_odd (c h : ℕ → R) (hc : SourceRecurrence c h) :
    sourceKernel c true = left (sourceSeries c) * right (sourceSeries c) *
      hankelSeries h 1 := by
  change bezout (-(PowerSeries.derivative R (sourceSeries c))) (sourceSeries c) = _
  rw [← hc, bezout_product]
  congr 1
  apply PowerSeries.ext
  intro i
  apply PowerSeries.ext
  intro j
  simp [divided, momentSeries, hankelSeries]

def coefficientBlock (f : BiSeries R) (r : ℕ) : Matrix (Fin r) (Fin r) R :=
  fun i j => PowerSeries.coeff j.val (PowerSeries.coeff i.val f)

def convolutionMatrix (c : ℕ → R) (r : ℕ) : Matrix (Fin r) (Fin r) R :=
  fun i j => if j.val ≤ i.val then c (i.val-j.val) else 0

def hankelMatrix (h : ℕ → R) (s r : ℕ) : Matrix (Fin r) (Fin r) R :=
  fun i j => h (i.val+j.val+s)

omit [IsDomain R] in
theorem coeff_product_finite (c f : PowerSeries R) (r : ℕ) (i : Fin r) :
    PowerSeries.coeff i.val (c*f) =
      ∑ a : Fin r, (if a.val ≤ i.val then PowerSeries.coeff (i.val-a.val) c else 0) *
        PowerSeries.coeff a.val f := by
  rw [PowerSeries.coeff_mul, ← Finset.Nat.sum_antidiagonal_swap]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [show (∑ a : Fin r, (if a.val ≤ i.val then PowerSeries.coeff (i.val-a.val) c else 0) *
      PowerSeries.coeff a.val f) =
    ∑ a ∈ Finset.range r, (if a ≤ i.val then PowerSeries.coeff (i.val-a) c else 0) *
      PowerSeries.coeff a f from Fin.sum_univ_eq_sum_range
        (fun a : ℕ => (if a ≤ i.val then PowerSeries.coeff (i.val-a) c else 0) *
          PowerSeries.coeff a f) r]
  symm
  calc
    (∑ a ∈ Finset.range r, (if a ≤ i.val then PowerSeries.coeff (i.val-a) c else 0) *
        PowerSeries.coeff a f) =
      ∑ a ∈ Finset.range (i.val+1), (if a ≤ i.val then
        PowerSeries.coeff (i.val-a) c else 0) * PowerSeries.coeff a f := by
          symm
          apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_of_lt i.isLt))
          intro a ha hnot
          have hlt : i.val < a := by simpa using hnot
          simp [not_le.mpr hlt]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      simp [show a ≤ i.val by simpa using ha]

omit [IsDomain R] in
theorem coefficient_congruence (c : ℕ → R) (h : ℕ → R) (s r : ℕ) :
    coefficientBlock (left (sourceSeries c) * right (sourceSeries c) * hankelSeries h s) r =
      convolutionMatrix c r * hankelMatrix h s r * (convolutionMatrix c r).transpose := by
  ext i j
  rw [show left (sourceSeries c) * right (sourceSeries c) * hankelSeries h s =
      left (sourceSeries c) * (right (sourceSeries c) * hankelSeries h s) by ring]
  change PowerSeries.coeff j.val (PowerSeries.coeff i.val
    (left (sourceSeries c) * (right (sourceSeries c) * hankelSeries h s))) = _
  rw [coeff_product_finite _ _ r i]
  simp only [left, PowerSeries.coeff_map, sourceSeries, PowerSeries.coeff_mk]
  simp only [map_sum, ite_mul, apply_ite, PowerSeries.coeff_C_mul, zero_mul, map_zero]
  change (∑ a : Fin r, (if a.val ≤ i.val then
      c (i.val-a.val) * PowerSeries.coeff j.val (PowerSeries.coeff a.val
        (right (sourceSeries c) * hankelSeries h s)) else 0)) = _
  simp only [Matrix.mul_apply, Matrix.transpose_apply, convolutionMatrix, hankelMatrix]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hai : a.val ≤ i.val
  · simp only [hai, ↓reduceIte]
    simp only [right, PowerSeries.coeff_C_mul]
    rw [coeff_product_finite _ _ r j]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    simp only [sourceSeries, hankelSeries, PowerSeries.coeff_mk]
    ring
  · simp [hai]

theorem source_bezout_to_hankel_congruence (c h : ℕ → R) (hc : SourceRecurrence c h)
    (oddSector : Bool) (r : ℕ) :
    coefficientBlock (sourceKernel c oddSector) r =
      convolutionMatrix c r * hankelMatrix h (if oddSector then 1 else 0) r *
        (convolutionMatrix c r).transpose := by
  cases oddSector
  · rw [source_kernel_even c h hc]
    exact coefficient_congruence c h 0 r
  · rw [source_kernel_odd c h hc]
    exact coefficient_congruence c h 1 r

omit [IsDomain R] in
theorem convolutionMatrix_det (c : ℕ → R) (r : ℕ) :
    (convolutionMatrix c r).det = c 0 ^ r := by
  have ht : (convolutionMatrix c r).BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hlt : i.val < j.val := hij
    simp [convolutionMatrix, not_le.mpr hlt]
  rw [Matrix.det_of_lowerTriangular _ ht]
  simp [convolutionMatrix]

theorem source_bezout_det (c h : ℕ → R) (hc : SourceRecurrence c h)
    (oddSector : Bool) (r : ℕ) :
    (coefficientBlock (sourceKernel c oddSector) r).det =
      c 0 ^ (2*r) * (hankelMatrix h (if oddSector then 1 else 0) r).det := by
  rw [source_bezout_to_hankel_congruence c h hc, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, convolutionMatrix_det]
  rw [show 2*r = r*2 by omega, pow_mul]
  ring

omit [IsDomain R] in
theorem divided_add (a b : PowerSeries R) : divided (a+b) = divided a + divided b := by
  apply PowerSeries.ext
  intro i
  apply PowerSeries.ext
  intro j
  simp [divided]

omit [IsDomain R] in
theorem bezout_add_left (a b c : PowerSeries R) :
    bezout (a+b) c = bezout a c + bezout b c := by
  simp only [bezout, divided_add, map_add]
  ring

omit [IsDomain R] in
theorem bezout_add_right (a b c : PowerSeries R) :
    bezout a (b+c) = bezout a b + bezout a c := by
  simp only [bezout, divided_add, map_add]
  ring

def mixedSourceKernel (c d : ℕ → R) (oddSector : Bool) : BiSeries R :=
  let C := sourceSeries c
  let A := -(PowerSeries.derivative R C)
  bezout (if oddSector then A else PowerSeries.X*A) (sourceSeries d)

omit [IsDomain R] in
theorem sourceSeries_add (c d : ℕ → R) : sourceSeries (c+d) = sourceSeries c + sourceSeries d := by
  apply PowerSeries.ext
  intro n
  simp [sourceSeries]

omit [IsDomain R] in
theorem mixedSourceKernel_add_left (c d e : ℕ → R) (b : Bool) :
    mixedSourceKernel (c+d) e b = mixedSourceKernel c e b + mixedSourceKernel d e b := by
  cases b <;>
    simp [mixedSourceKernel, sourceSeries_add, map_add, mul_add, bezout_add_left, add_comm]

omit [IsDomain R] in
theorem mixedSourceKernel_add_right (c d e : ℕ → R) (b : Bool) :
    mixedSourceKernel c (d+e) b = mixedSourceKernel c d b + mixedSourceKernel c e b := by
  simp [mixedSourceKernel, sourceSeries_add, bezout_add_right]

omit [IsDomain R] in
/-- All four ordered head/tail terms remain. No term is assigned a sign. -/
theorem sourceKernel_head_tail (head tail : ℕ → R) (b : Bool) :
    sourceKernel (head+tail) b =
      mixedSourceKernel head head b + mixedSourceKernel head tail b +
      mixedSourceKernel tail head b + mixedSourceKernel tail tail b := by
  change mixedSourceKernel (head+tail) (head+tail) b = _
  rw [mixedSourceKernel_add_left, mixedSourceKernel_add_right,
    mixedSourceKernel_add_right]
  abel

theorem source_bezout_posSemidef_iff (c h : ℕ → ℝ) (hc : SourceRecurrence c h)
    (h0 : c 0 ≠ 0) (b : Bool) (r : ℕ) :
    (coefficientBlock (sourceKernel c b) r).PosSemidef ↔
      (hankelMatrix h (if b then 1 else 0) r).PosSemidef := by
  have ht : IsUnit (convolutionMatrix c r) := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    rw [convolutionMatrix_det]
    exact isUnit_iff_ne_zero.mpr (pow_ne_zero r h0)
  rw [source_bezout_to_hankel_congruence c h hc]
  convert Matrix.IsUnit.posSemidef_star_right_conjugate_iff ht using 1
  simp [Matrix.star_eq_conjTranspose]

theorem source_bezout_posDef_iff (c h : ℕ → ℝ) (hc : SourceRecurrence c h)
    (h0 : c 0 ≠ 0) (b : Bool) (r : ℕ) :
    (coefficientBlock (sourceKernel c b) r).PosDef ↔
      (hankelMatrix h (if b then 1 else 0) r).PosDef := by
  have ht : IsUnit (convolutionMatrix c r) := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    rw [convolutionMatrix_det]
    exact isUnit_iff_ne_zero.mpr (pow_ne_zero r h0)
  rw [source_bezout_to_hankel_congruence c h hc]
  convert Matrix.IsUnit.posDef_star_right_conjugate_iff ht using 1
  simp [Matrix.star_eq_conjTranspose]

end
end CarrySourceBezout
