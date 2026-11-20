import TwoEvenSourceMargin

/-!
Native mixed pair transport in original source coordinates. The Toeplitz
camera factor is not discarded. This module does not assert any sign.
-/
namespace CarrySourceBezout
open CarrySelfAdjointOperator Matrix
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 2000000

/-- Inverse transpose transport from native Hankel coordinates to the
original division-free source Bézout block. -/
def mixedSourceLift (r : ℕ) (x : Fin r → ℝ) : Fin r → ℝ :=
  ((convolutionMatrix nativeC r).transpose)⁻¹ *ᵥ x

theorem mixedSourceLift_transport (r : ℕ) (x : Fin r → ℝ) :
    (convolutionMatrix nativeC r).transpose *ᵥ mixedSourceLift r x = x := by
  have hC : nativeC 0 ≠ 0 :=
    completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero
  have hT : IsUnit (convolutionMatrix nativeC r).transpose := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    rw [Matrix.det_transpose]
    exact (Matrix.isUnit_iff_isUnit_det _).mp
      (convolutionMatrix_isUnit nativeC hC r)
  letI := hT.invertible
  simp only [mixedSourceLift, Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible,
    Matrix.one_mulVec]

/-- Literal native kernel, two arbitrary independent Hankel vectors. -/
theorem native_mixed_pair_transport (b : Bool) (r : ℕ)
    (x y : Fin r → ℝ) :
    matrixPair (sourceMomentMatrix nativeH (if b then 1 else 0) r) x y =
      matrixPair (coefficientBlock (sourceKernel nativeC b) r)
        (mixedSourceLift r x) (mixedSourceLift r y) := by
  rw [native_source_bezout_congruence, congruence_pair,
    mixedSourceLift_transport, mixedSourceLift_transport]

/-- Complete four-term TFVD reconstruction of a mixed native moment pair.
Retains original C3 camera, completed trace, two cutoffs and both legs. -/
theorem native_mixed_tfvd_four_terms (M P : ℕ) (b : Bool) (r : ℕ)
    (x y : Fin r → ℝ) :
    (matrixPair (sourceMomentMatrix nativeH (if b then 1 else 0) r) x y : ℂ) =
      literalTerm M P true true b r (mixedSourceLift r x) (mixedSourceLift r y) +
      literalTerm M P true false b r (mixedSourceLift r x) (mixedSourceLift r y) +
      literalTerm M P false true b r (mixedSourceLift r x) (mixedSourceLift r y) +
      literalTerm M P false false b r (mixedSourceLift r x) (mixedSourceLift r y) := by
  rw [native_mixed_pair_transport b r x y]
  exact literal_four_terms M P b r (mixedSourceLift r x) (mixedSourceLift r y)


/-- Zero address padding: the shifted-two moment matrix is the original
even matrix on the subspace of vectors with a zero first address. -/
theorem native_shift_two_mixed (m : ℕ → ℝ) (s n : ℕ)
    (x y : Fin n → ℝ) :
    matrixPair (sourceMomentMatrix m s (n+1)) (Fin.cons 0 x) (Fin.cons 0 y) =
      matrixPair (sourceMomentMatrix m (s+2) n) x y := by
  simp only [matrixPair, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    Fin.cons_zero, Fin.cons_succ, zero_mul, mul_zero, zero_add,
    sourceMomentMatrix]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have he : i.succ.val + j.succ.val + s = i.val + j.val + (s+2) := by
    simp; omega
  rw [he]

/-- The constant polynomial in the old shifted prefix, NOT the primitive
geometric C2 seed or the first material TFVD edge. -/
def firstPolynomial (n : ℕ) : Fin (n+1) → ℝ :=
  fun i => if i = 0 then 1 else 0

/-- The signed scalar that was previously explored numerically. -/
def nativeMixedU (s n : ℕ) (r : Fin (n+1) → ℝ) : ℝ :=
  ∑ i : Fin (n+1), r i * nativeH (s+1+i.val)

theorem nativeMixedU_pair (s n : ℕ) (r : Fin (n+1) → ℝ) :
    nativeMixedU s n r =
      matrixPair (sourceMomentMatrix nativeH (s+1) (n+1))
        r (firstPolynomial n) := by
  simp [nativeMixedU, matrixPair, sourceMomentMatrix, Matrix.mulVec,
    dotProduct, firstPolynomial, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- For even Schur (s=0), the old shifted prefix is the native ODD
source chart (b=true). -/
theorem nativeMixedU_even_four_terms (M P n : ℕ) (r : Fin (n+1) → ℝ) :
    (nativeMixedU 0 n r : ℂ) =
      literalTerm M P true true true (n+1)
        (mixedSourceLift (n+1) r) (mixedSourceLift (n+1) (firstPolynomial n)) +
      literalTerm M P true false true (n+1)
        (mixedSourceLift (n+1) r) (mixedSourceLift (n+1) (firstPolynomial n)) +
      literalTerm M P false true true (n+1)
        (mixedSourceLift (n+1) r) (mixedSourceLift (n+1) (firstPolynomial n)) +
      literalTerm M P false false true (n+1)
        (mixedSourceLift (n+1) r) (mixedSourceLift (n+1) (firstPolynomial n)) := by
  rw [nativeMixedU_pair]
  exact native_mixed_tfvd_four_terms M P true (n+1) r (firstPolynomial n)

/-- For odd Schur (s=1), the shifted prefix H2 is EXACTLY the native
EVEN chart H0 with a zero first address. -/
theorem nativeMixedU_odd_four_terms (M P n : ℕ) (r : Fin (n+1) → ℝ) :
    (nativeMixedU 1 n r : ℂ) =
      literalTerm M P true true false (n+2)
        (mixedSourceLift (n+2) (Fin.cons 0 r))
        (mixedSourceLift (n+2) (Fin.cons 0 (firstPolynomial n))) +
      literalTerm M P true false false (n+2)
        (mixedSourceLift (n+2) (Fin.cons 0 r))
        (mixedSourceLift (n+2) (Fin.cons 0 (firstPolynomial n))) +
      literalTerm M P false true false (n+2)
        (mixedSourceLift (n+2) (Fin.cons 0 r))
        (mixedSourceLift (n+2) (Fin.cons 0 (firstPolynomial n))) +
      literalTerm M P false false false (n+2)
        (mixedSourceLift (n+2) (Fin.cons 0 r))
        (mixedSourceLift (n+2) (Fin.cons 0 (firstPolynomial n))) := by
  rw [nativeMixedU_pair]
  rw [← native_shift_two_mixed nativeH 0 (n+1) r (firstPolynomial n)]
  exact native_mixed_tfvd_four_terms M P false (n+2)
    (Fin.cons 0 r) (Fin.cons 0 (firstPolynomial n))


/-- A truly mixed, source-first TFVD error inequality; its vectors are
the transformed originals and need not be equal or monic. -/
theorem native_mixed_tfvd_error (M P : ℕ) (b : Bool) (r : ℕ)
    (x y : Fin r → ℝ) :
    ‖(matrixPair (sourceMomentMatrix nativeH (if b then 1 else 0) r) x y : ℂ) -
       literalTerm M P true true b r (mixedSourceLift r x) (mixedSourceLift r y)‖ ≤
      literalErrorBudget M P b r (mixedSourceLift r x) (mixedSourceLift r y) := by
  rw [native_mixed_pair_transport]
  exact literal_error_bound M P b r (mixedSourceLift r x) (mixedSourceLift r y)

/-- Error for the even sector u in its actual ODD Bézout source chart. -/
theorem nativeMixedU_even_error (M P n : ℕ) (r : Fin (n+1) → ℝ) :
    ‖(nativeMixedU 0 n r : ℂ) -
       literalTerm M P true true true (n+1)
         (mixedSourceLift (n+1) r) (mixedSourceLift (n+1) (firstPolynomial n))‖ ≤
       literalErrorBudget M P true (n+1)
         (mixedSourceLift (n+1) r) (mixedSourceLift (n+1) (firstPolynomial n)) := by
  rw [nativeMixedU_pair]
  exact native_mixed_tfvd_error M P true (n+1) r (firstPolynomial n)

/-- Error for the odd sector u in its exact zero-padded EVEN source chart. -/
theorem nativeMixedU_odd_error (M P n : ℕ) (r : Fin (n+1) → ℝ) :
    ‖(nativeMixedU 1 n r : ℂ) -
       literalTerm M P true true false (n+2)
         (mixedSourceLift (n+2) (Fin.cons 0 r))
         (mixedSourceLift (n+2) (Fin.cons 0 (firstPolynomial n)))‖ ≤
       literalErrorBudget M P false (n+2)
         (mixedSourceLift (n+2) (Fin.cons 0 r))
         (mixedSourceLift (n+2) (Fin.cons 0 (firstPolynomial n))) := by
  rw [nativeMixedU_pair]
  rw [← native_shift_two_mixed nativeH 0 (n+1) r (firstPolynomial n)]
  exact native_mixed_tfvd_error M P false (n+2)
    (Fin.cons 0 r) (Fin.cons 0 (firstPolynomial n))


/-- The true real scalar obeys the real-part head budget, after preserving
all four complex TFVD crossings and the native source lift. -/
theorem nativeMixedU_even_real_error (M P n : ℕ) (r : Fin (n+1) → ℝ) :
    |nativeMixedU 0 n r -
       (literalTerm M P true true true (n+1)
         (mixedSourceLift (n+1) r) (mixedSourceLift (n+1) (firstPolynomial n))).re| ≤
       literalErrorBudget M P true (n+1)
         (mixedSourceLift (n+1) r) (mixedSourceLift (n+1) (firstPolynomial n)) := by
  have h := nativeMixedU_even_error M P n r
  have ha := Complex.abs_re_le_norm
    (((nativeMixedU 0 n r : ℝ):ℂ) -
       literalTerm M P true true true (n+1)
         (mixedSourceLift (n+1) r) (mixedSourceLift (n+1) (firstPolynomial n)))
  exact (by simpa only [Complex.sub_re, Complex.ofReal_re] using ha.trans h)

theorem nativeMixedU_odd_real_error (M P n : ℕ) (r : Fin (n+1) → ℝ) :
    |nativeMixedU 1 n r -
       (literalTerm M P true true false (n+2)
         (mixedSourceLift (n+2) (Fin.cons 0 r))
         (mixedSourceLift (n+2) (Fin.cons 0 (firstPolynomial n)))).re| ≤
       literalErrorBudget M P false (n+2)
         (mixedSourceLift (n+2) (Fin.cons 0 r))
         (mixedSourceLift (n+2) (Fin.cons 0 (firstPolynomial n))) := by
  have h := nativeMixedU_odd_error M P n r
  have ha := Complex.abs_re_le_norm
    (((nativeMixedU 1 n r : ℝ):ℂ) -
       literalTerm M P true true false (n+2)
         (mixedSourceLift (n+2) (Fin.cons 0 r))
         (mixedSourceLift (n+2) (Fin.cons 0 (firstPolynomial n))))
  exact (by simpa only [Complex.sub_re, Complex.ofReal_re] using ha.trans h)


/-- Repartition with an arbitrary ORIGINAL completed boundary U, without
assuming any new Gram sign. This is the exact mixed-vector extension of the
source's C3 accelerated ledger. -/
theorem native_mixed_repartition_error (M : ℕ) (U : ℕ → ℂ)
    (b : Bool) (r : ℕ) (x y : Fin r → ℝ) :
    ‖(matrixPair (sourceMomentMatrix nativeH (if b then 1 else 0) r) x y : ℂ) -
      coefficientPair (literalHead M+U) (literalHead M+U) b r
        (mixedSourceLift r x) (mixedSourceLift r y)‖ ≤
      splitErrorBudget (literalHead M+U) (literalTail M-U) b r
        (mixedSourceLift r x) (mixedSourceLift r y) := by
  let X := mixedSourceLift r x
  let Y := mixedSourceLift r y
  have hsum :
      (literalHead M+U)+(literalTail M-U) =
        (fun n => (nativeC n : ℂ)) := by
    funext k
    have hs := congrFun (literal_head_tail M) k
    simp only [Pi.add_apply, Pi.sub_apply] at hs ⊢
    calc
      literalHead M k + U k + (literalTail M k - U k) =
          literalHead M k + literalTail M k := by ring
      _ = (nativeC k : ℂ) := hs.symm
  have hsource : coefficientPair ((literalHead M+U)+(literalTail M-U))
      ((literalHead M+U)+(literalTail M-U)) b r X Y =
      (matrixPair (coefficientBlock (sourceKernel nativeC b) r) X Y : ℂ) := by
    rw [hsum]
    unfold coefficientPair
    change complexPair (coefficientBlock
      (sourceKernel (fun n => (nativeC n : ℂ)) b) r)
      (fun i => (X i : ℂ)) (fun j => (Y j : ℂ)) = _
    have hm := sourceKernel_map Complex.ofRealHom nativeC b
    change sourceKernel (fun n => (nativeC n : ℂ)) b = _ at hm
    rw [hm, coefficientBlock_map]
    exact complexPair_real _ _ _
  rw [native_mixed_pair_transport b r x y]
  change ‖(matrixPair (coefficientBlock (sourceKernel nativeC b) r) X Y : ℂ) -
      coefficientPair (literalHead M+U) (literalHead M+U) b r X Y‖ ≤
      splitErrorBudget (literalHead M+U) (literalTail M-U) b r X Y
  rw [← hsource]
  exact split_error_bound (literalHead M+U) (literalTail M-U) b r X Y


/-- Accelerated mixed-u budget in the odd source chart (even Schur). -/
theorem nativeMixedU_even_repartition_real_error
    (M n : ℕ) (U : ℕ → ℂ) (r : Fin (n+1) → ℝ) :
    |nativeMixedU 0 n r -
      (coefficientPair (literalHead M+U) (literalHead M+U) true (n+1)
        (mixedSourceLift (n+1) r) (mixedSourceLift (n+1) (firstPolynomial n))).re| ≤
      splitErrorBudget (literalHead M+U) (literalTail M-U) true (n+1)
        (mixedSourceLift (n+1) r) (mixedSourceLift (n+1) (firstPolynomial n)) := by
  have h := native_mixed_repartition_error M U true (n+1) r (firstPolynomial n)
  rw [nativeMixedU_pair]
  have ha := Complex.abs_re_le_norm
    (((matrixPair (sourceMomentMatrix nativeH 1 (n+1)) r (firstPolynomial n) : ℝ):ℂ) -
      coefficientPair (literalHead M+U) (literalHead M+U) true (n+1)
        (mixedSourceLift (n+1) r) (mixedSourceLift (n+1) (firstPolynomial n)))
  simpa only [Complex.sub_re, Complex.ofReal_re] using ha.trans h

/-- Accelerated mixed-u budget in the even source chart, with its
exact zero-address embedding (odd Schur). -/
theorem nativeMixedU_odd_repartition_real_error
    (M n : ℕ) (U : ℕ → ℂ) (r : Fin (n+1) → ℝ) :
    |nativeMixedU 1 n r -
      (coefficientPair (literalHead M+U) (literalHead M+U) false (n+2)
        (mixedSourceLift (n+2) (Fin.cons 0 r))
        (mixedSourceLift (n+2) (Fin.cons 0 (firstPolynomial n)))).re| ≤
      splitErrorBudget (literalHead M+U) (literalTail M-U) false (n+2)
        (mixedSourceLift (n+2) (Fin.cons 0 r))
        (mixedSourceLift (n+2) (Fin.cons 0 (firstPolynomial n))) := by
  have h := native_mixed_repartition_error M U false (n+2)
    (Fin.cons 0 r) (Fin.cons 0 (firstPolynomial n))
  rw [nativeMixedU_pair, ← native_shift_two_mixed nativeH 0 (n+1)
    r (firstPolynomial n)]
  have ha := Complex.abs_re_le_norm
    (((matrixPair (sourceMomentMatrix nativeH 0 (n+2))
      (Fin.cons 0 r) (Fin.cons 0 (firstPolynomial n)) : ℝ):ℂ) -
      coefficientPair (literalHead M+U) (literalHead M+U) false (n+2)
        (mixedSourceLift (n+2) (Fin.cons 0 r))
        (mixedSourceLift (n+2) (Fin.cons 0 (firstPolynomial n))))
  simpa only [Complex.sub_re, Complex.ofReal_re] using ha.trans h

end
end CarrySourceBezout
