import NativeMixedU

/-!
Exactly correlated signed source functional S = alpha * B - beta*a * p.
The two terms must share the SAME completed source jets, tail and boundary.
No new source positivity is assumed. Weighted coefficients are arbitrary reals,
allowing a to be either sign.
-/
namespace CarrySourceBezout
open CarrySelfAdjointOperator Matrix
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 1800000

def signedSourcePair (alpha betaA : ℝ)
    (bB bP : Bool) (rB rP : ℕ)
    (zB : Fin rB → ℝ) (zP : Fin rP → ℝ)
    (left right : ℕ → ℂ) : ℂ :=
  (alpha:ℂ)*coefficientPair left right bB rB zB zB -
  (betaA:ℂ)*coefficientPair left right bP rP zP zP

def signedSourceLinear (alpha betaA : ℝ)
    (bB bP : Bool) (rB rP : ℕ)
    (zB : Fin rB → ℝ) (zP : Fin rP → ℝ)
    (head tail : ℕ → ℂ) : ℂ :=
  signedSourcePair alpha betaA bB bP rB rP zB zP head tail +
  signedSourcePair alpha betaA bB bP rB rP zB zP tail head

/-- Exact source-level correlated splitting. HT and TH are joined BEFORE
taking any norms or budgets. Different parity/address dimensions are retained. -/
theorem signed_source_four_terms
    (alpha betaA : ℝ) (bB bP : Bool) (rB rP : ℕ)
    (zB : Fin rB → ℝ) (zP : Fin rP → ℝ)
    (H T : ℕ → ℂ) :
    signedSourcePair alpha betaA bB bP rB rP zB zP (H+T) (H+T) =
      signedSourcePair alpha betaA bB bP rB rP zB zP H H +
      signedSourceLinear alpha betaA bB bP rB rP zB zP H T +
      signedSourcePair alpha betaA bB bP rB rP zB zP T T := by
  simp only [signedSourcePair, signedSourceLinear]
  rw [coefficientPair_four_terms H T H T bB rB zB zB,
      coefficientPair_four_terms H T H T bP rP zP zP]
  ring

/-- The exact joint source error has only two terms, a linear response to
the ONE shared tail, and a quadratic tail-tail remainder. -/
theorem signed_source_joint_error_bound
    (alpha betaA : ℝ) (bB bP : Bool) (rB rP : ℕ)
    (zB : Fin rB → ℝ) (zP : Fin rP → ℝ)
    (H T : ℕ → ℂ) :
    ‖signedSourcePair alpha betaA bB bP rB rP zB zP (H+T) (H+T) -
      signedSourcePair alpha betaA bB bP rB rP zB zP H H‖ ≤
      ‖signedSourceLinear alpha betaA bB bP rB rP zB zP H T‖ +
      ‖signedSourcePair alpha betaA bB bP rB rP zB zP T T‖ := by
  rw [signed_source_four_terms]
  convert norm_add_le
    (signedSourceLinear alpha betaA bB bP rB rP zB zP H T)
    (signedSourcePair alpha betaA bB bP rB rP zB zP T T) using 1
  ring

/-- The exact same native completed source, mapped into the complex field. -/
theorem native_coefficientPair_real (b : Bool) (r : ℕ)
    (x y : Fin r → ℝ) :
    coefficientPair (fun k => (nativeC k : ℂ)) (fun k => (nativeC k : ℂ)) b r x y =
      (matrixPair (coefficientBlock (sourceKernel nativeC b) r) x y : ℂ) := by
  unfold coefficientPair
  change complexPair (coefficientBlock
    (sourceKernel (fun k => (nativeC k : ℂ)) b) r)
    (fun i => (x i : ℂ)) (fun j => (y j : ℂ)) = _
  have hm := sourceKernel_map Complex.ofRealHom nativeC b
  change sourceKernel (fun k => (nativeC k : ℂ)) b = _ at hm
  rw [hm, coefficientBlock_map]
  exact complexPair_real _ _ _

/-- All signs survive; no triangle loss between alpha*B and beta*a*p. -/
theorem signed_source_native_even (n : ℕ)
    (v : Fin (n+1) → ℝ) (alpha betaA : ℝ) :
    ((alpha*matrixPair (sourceMomentMatrix nativeH 1 (n+1)) v v -
        betaA*matrixPair (sourceMomentMatrix nativeH 0 (n+1)) v v : ℝ):ℂ) =
      signedSourcePair alpha betaA true false (n+1) (n+1)
        (mixedSourceLift (n+1) v) (mixedSourceLift (n+1) v)
        (fun k => (nativeC k : ℂ)) (fun k => (nativeC k : ℂ)) := by
  have hB : matrixPair (sourceMomentMatrix nativeH 1 (n+1)) v v =
      matrixPair (coefficientBlock (sourceKernel nativeC true) (n+1))
        (mixedSourceLift (n+1) v) (mixedSourceLift (n+1) v) := by
    simpa using native_mixed_pair_transport true (n+1) v v
  have hP : matrixPair (sourceMomentMatrix nativeH 0 (n+1)) v v =
      matrixPair (coefficientBlock (sourceKernel nativeC false) (n+1))
        (mixedSourceLift (n+1) v) (mixedSourceLift (n+1) v) := by
    simpa using native_mixed_pair_transport false (n+1) v v
  simp only [signedSourcePair]
  rw [native_coefficientPair_real true (n+1) (mixedSourceLift (n+1) v) (mixedSourceLift (n+1) v),
      native_coefficientPair_real false (n+1) (mixedSourceLift (n+1) v) (mixedSourceLift (n+1) v)]
  rw [hB, hP]
  push_cast
  ring

/-- The B term in odd Schur is H2 and hence needs one ZERO inserted into
the even source chart; the p term remains on the odd source chart. -/
theorem signed_source_native_odd (n : ℕ)
    (v : Fin (n+1) → ℝ) (alpha betaA : ℝ) :
    ((alpha*matrixPair (sourceMomentMatrix nativeH 2 (n+1)) v v -
        betaA*matrixPair (sourceMomentMatrix nativeH 1 (n+1)) v v : ℝ):ℂ) =
      signedSourcePair alpha betaA false true (n+2) (n+1)
        (mixedSourceLift (n+2) (Fin.cons 0 v)) (mixedSourceLift (n+1) v)
        (fun k => (nativeC k : ℂ)) (fun k => (nativeC k : ℂ)) := by
  have hB : matrixPair (sourceMomentMatrix nativeH 0 (n+2))
        (Fin.cons 0 v) (Fin.cons 0 v) =
      matrixPair (coefficientBlock (sourceKernel nativeC false) (n+2))
        (mixedSourceLift (n+2) (Fin.cons 0 v))
        (mixedSourceLift (n+2) (Fin.cons 0 v)) := by
    simpa using native_mixed_pair_transport false (n+2) (Fin.cons 0 v) (Fin.cons 0 v)
  have hP : matrixPair (sourceMomentMatrix nativeH 1 (n+1)) v v =
      matrixPair (coefficientBlock (sourceKernel nativeC true) (n+1))
        (mixedSourceLift (n+1) v) (mixedSourceLift (n+1) v) := by
    simpa using native_mixed_pair_transport true (n+1) v v
  have hShift := native_shift_two_mixed nativeH 0 (n+1) v v
  simp only [signedSourcePair]
  rw [native_coefficientPair_real false (n+2) (mixedSourceLift (n+2) (Fin.cons 0 v))
        (mixedSourceLift (n+2) (Fin.cons 0 v)),
      native_coefficientPair_real true (n+1) (mixedSourceLift (n+1) v) (mixedSourceLift (n+1) v)]
  rw [← hShift, hB, hP]
  push_cast
  ring

end
end CarrySourceBezout
