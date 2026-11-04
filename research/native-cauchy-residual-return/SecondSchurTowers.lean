import SecondSchur
import Mathlib.Algebra.MvPolynomial.Basic

/-!
# Polynomial coefficient form of the local Cayley moment series

Each convergent Cayley summand has a canonical homogeneous polynomial
extension.  Its coefficients display the even-even and odd-odd Hankel towers.
-/

open scoped BigOperators ComplexConjugate

namespace CarryCauchyResidual

open CarrySelfAdjointOperator Filter
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

/-- The degree `2n` homogeneous polynomial extension of the nth Cayley
moment summand.  Its scalar coefficient is the original canonical moment. -/
def nativePhysicalCayleyHomogeneousPolynomial (n : ℕ) :
    MvPolynomial (Fin 2) ℂ :=
  ∑ r ∈ Finset.range (2*n+1),
    MvPolynomial.monomial
      (Finsupp.single (0 : Fin 2) (2*n-r) +
        Finsupp.single (1 : Fin 2) r)
      (4 * (-1:ℂ)^(n+r) *
        (canonicalCompletedNativeLogDerivativeMoment n : ℂ))

/-- The finite alternating quotient polynomial at a pair of complex points. -/
def nativePhysicalCayleyGeometricPolynomial (s t : ℂ) (n : ℕ) : ℂ :=
  ∑ r ∈ Finset.range (2*n+1),
    (-1:ℂ)^r * s^(2*n-r) * t^r

private theorem nativePhysicalCayleyExponent_eval
    (s t : ℂ) (a b : ℕ) :
    (Finsupp.single (0 : Fin 2) a + Finsupp.single (1 : Fin 2) b).prod
        (fun i e => (if i = 0 then s else t)^e) = s^a * t^b := by
  rw [Finsupp.prod_add_index' (h_zero := by
      intro i
      by_cases hi : i = 0 <;> simp [hi]) (h_add := by
      intro i m₁ m₂
      by_cases hi : i = 0 <;> simp [hi, pow_add])]
  simp [Finsupp.prod_single_index]

/-- Evaluation of the homogeneous polynomial summand is the finite
alternating quotient polynomial multiplied by its canonical moment. -/
theorem nativePhysicalCayleyHomogeneousPolynomial_eval
    (s t : ℂ) (n : ℕ) :
    MvPolynomial.eval (fun i : Fin 2 => if i = 0 then s else t)
        (nativePhysicalCayleyHomogeneousPolynomial n) =
      4 * (-1:ℂ)^n *
        (canonicalCompletedNativeLogDerivativeMoment n : ℂ) *
          nativePhysicalCayleyGeometricPolynomial s t n := by
  classical
  simp only [nativePhysicalCayleyHomogeneousPolynomial,
    MvPolynomial.eval_sum, MvPolynomial.eval_monomial]
  simp_rw [nativePhysicalCayleyExponent_eval]
  simp [nativePhysicalCayleyGeometricPolynomial, pow_add,
    Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

/-- Recurrence for the finite alternating quotient polynomial. -/
theorem nativePhysicalCayleyGeometricPolynomial_succ
    (s t : ℂ) (n : ℕ) :
    nativePhysicalCayleyGeometricPolynomial s t (n+1) =
      s^2 * nativePhysicalCayleyGeometricPolynomial s t n -
        s * t^(2*n+1) + t^(2*n+2) := by
  classical
  unfold nativePhysicalCayleyGeometricPolynomial
  have hrange : 2*(n+1)+1 = (2*n+1)+2 := by omega
  rw [hrange, Finset.sum_range_succ, Finset.sum_range_succ]
  rw [show 2*(n+1) = 2*n+2 by omega]
  have hcore :
      (∑ r ∈ Finset.range (2*n+1),
        (-1:ℂ)^r * s^(2*n+2-r) * t^r) =
        s^2 * (∑ r ∈ Finset.range (2*n+1),
          (-1:ℂ)^r * s^(2*n-r) * t^r) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    have hrle : r ≤ 2*n := by
      have hr' := Finset.mem_range.mp hr
      omega
    have hexp : 2*n+2-r = 2+(2*n-r) := by omega
    rw [hexp, pow_add]
    ring
  have hsign₁ : (-1:ℂ)^(2*n+1) = -1 := by
    rw [pow_add, pow_mul]
    norm_num
  have hsign₂ : (-1:ℂ)^(2*n+2) = 1 := by
    rw [show 2*n+2 = 2*(n+1) by omega, pow_mul]
    norm_num
  rw [hcore, hsign₁, hsign₂]
  simp
  ring

/-- Multiplying the finite alternating sum by `s+t` recovers the sum of odd
powers, including the removable value at `s+t=0`. -/
theorem nativePhysicalCayleyGeometricPolynomial_mul
    (s t : ℂ) (n : ℕ) :
    (s+t) * nativePhysicalCayleyGeometricPolynomial s t n =
      s^(2*n+1) + t^(2*n+1) := by
  induction n with
  | zero =>
      simp [nativePhysicalCayleyGeometricPolynomial]
  | succ n ih =>
      have hdegree : 2*(n+1)+1 = 2*n+3 := by omega
      rw [hdegree, nativePhysicalCayleyGeometricPolynomial_succ]
      calc
        (s+t) *
            (s^2 * nativePhysicalCayleyGeometricPolynomial s t n -
              s*t^(2*n+1) + t^(2*n+2)) =
          s^2 * ((s+t) * nativePhysicalCayleyGeometricPolynomial s t n) +
            (s+t) * (-s*t^(2*n+1) + t^(2*n+2)) := by ring
        _ = s^2 * (s^(2*n+1) + t^(2*n+1)) +
            (s+t) * (-s*t^(2*n+1) + t^(2*n+2)) := by rw [ih]
        _ = s^(2*n+3) + t^(2*n+3) := by ring

/-- Away from the removable diagonal, the original rational moment summand
is exactly the evaluation of its homogeneous polynomial extension. -/
theorem nativePhysicalCayleyAnalyticMomentTerm_eq_homogeneous_eval
    (s t : ℝ) (n : ℕ) (hst : s+t ≠ 0) :
    nativePhysicalCayleyAnalyticMomentTerm s t n =
      MvPolynomial.eval
        (fun i : Fin 2 => if i = 0 then (s : ℂ) else (t : ℂ))
        (nativePhysicalCayleyHomogeneousPolynomial n) := by
  rw [nativePhysicalCayleyHomogeneousPolynomial_eval]
  have hden : ((s+t:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hst
  have hquot :
      (((s:ℂ)^(2*n+1) + (t:ℂ)^(2*n+1)) /
          ((s+t:ℝ):ℂ)) =
        nativePhysicalCayleyGeometricPolynomial (s:ℂ) (t:ℂ) n := by
    field_simp [hden]
    rw [← nativePhysicalCayleyGeometricPolynomial_mul]
    rw [Complex.ofReal_add]
  dsimp [nativePhysicalCayleyAnalyticMomentTerm]
  rw [hquot]

/-- The actual local kernel is a convergent sum of the homogeneous
polynomials whose coefficients are the two moment towers. -/
theorem nativePhysicalCayleyHomogeneousPolynomialSeries_hasSum
    (s t : ℝ)
    (hs : HasSum (fun n : ℕ =>
      2 * (s : ℂ) * (-(s : ℂ)^2)^n *
        (canonicalCompletedNativeLogDerivativeMoment n : ℂ))
      (nativePhysicalCayleyRho s))
    (ht : HasSum (fun n : ℕ =>
      2 * (t : ℂ) * (-(t : ℂ)^2)^n *
        (canonicalCompletedNativeLogDerivativeMoment n : ℂ))
      (nativePhysicalCayleyRho t))
    (hst : s+t ≠ 0) :
    HasSum
      (fun n : ℕ => MvPolynomial.eval
        (fun i : Fin 2 => if i = 0 then (s : ℂ) else (t : ℂ))
        (nativePhysicalCayleyHomogeneousPolynomial n))
      (nativePhysicalCayleyAnalyticKernel s t) := by
  refine HasSum.congr_fun
    (nativePhysicalCayleyAnalyticKernel_hasSum s t hs ht hst) (fun n => ?_)
  exact (nativePhysicalCayleyAnalyticMomentTerm_eq_homogeneous_eval s t n hst).symm

private theorem nativePhysicalCayleyExponentPair_iff
    (n a b r : ℕ) (hr : r ≤ 2*n) :
    Finsupp.single (0 : Fin 2) (2*n-r) +
        Finsupp.single (1 : Fin 2) r =
      Finsupp.single (0 : Fin 2) a + Finsupp.single (1 : Fin 2) b ↔
    r = b ∧ a+b=2*n := by
  constructor
  · intro h
    have h0 : 2*n-r = a := by
      have h' := congrArg (fun m : Fin 2 →₀ ℕ => m 0) h
      simpa using h'
    have h1 : r = b := by
      have h' := congrArg (fun m : Fin 2 →₀ ℕ => m 1) h
      simpa using h'
    constructor
    · exact h1
    · omega
  · rintro ⟨hrb, hab⟩
    subst r
    have hsub : 2*n-b = a := by omega
    ext x
    fin_cases x <;> simp [hsub]

/-- Exact coefficient formula for one homogeneous Cayley summand. -/
theorem nativePhysicalCayleyHomogeneousPolynomial_coeff
    (n a b : ℕ) :
    MvPolynomial.coeff
        (Finsupp.single (0 : Fin 2) a + Finsupp.single (1 : Fin 2) b)
        (nativePhysicalCayleyHomogeneousPolynomial n) =
      if a+b=2*n then
        4 * (-1:ℂ)^(n+b) *
          (canonicalCompletedNativeLogDerivativeMoment n : ℂ)
      else 0 := by
  classical
  unfold nativePhysicalCayleyHomogeneousPolynomial
  rw [MvPolynomial.coeff_sum]
  by_cases hab : a+b=2*n
  · have hb : b ∈ Finset.range (2*n+1) := by
      simp
      omega
    have hble : b ≤ 2*n := by omega
    rw [if_pos hab]
    have hmain :
        Finsupp.single (0 : Fin 2) (2*n-b) +
            Finsupp.single (1 : Fin 2) b =
          Finsupp.single (0 : Fin 2) a +
            Finsupp.single (1 : Fin 2) b :=
      (nativePhysicalCayleyExponentPair_iff n a b b hble).2 ⟨rfl, hab⟩
    calc
      (∑ r ∈ Finset.range (2*n+1),
          MvPolynomial.coeff
            (Finsupp.single (0 : Fin 2) a + Finsupp.single (1 : Fin 2) b)
            (MvPolynomial.monomial
              (Finsupp.single (0 : Fin 2) (2*n-r) + Finsupp.single (1 : Fin 2) r)
              (4 * (-1:ℂ)^(n+r) *
                (canonicalCompletedNativeLogDerivativeMoment n : ℂ)))) =
        MvPolynomial.coeff
          (Finsupp.single (0 : Fin 2) a + Finsupp.single (1 : Fin 2) b)
          (MvPolynomial.monomial
            (Finsupp.single (0 : Fin 2) (2*n-b) + Finsupp.single (1 : Fin 2) b)
            (4 * (-1:ℂ)^(n+b) *
              (canonicalCompletedNativeLogDerivativeMoment n : ℂ))) := by
        apply Finset.sum_eq_single b
        · intro r hr hne
          have hrle : r ≤ 2*n := by
            have hr' := Finset.mem_range.mp hr
            omega
          have hneq :
              Finsupp.single (0 : Fin 2) (2*n-r) + Finsupp.single (1 : Fin 2) r ≠
                Finsupp.single (0 : Fin 2) a + Finsupp.single (1 : Fin 2) b := by
            intro heq
            exact hne ((nativePhysicalCayleyExponentPair_iff n a b r hrle).mp heq).1
          rw [MvPolynomial.coeff_monomial, if_neg hneq]
        · intro hnot
          exact (hnot hb).elim
      _ = 4 * (-1:ℂ)^(n+b) *
          (canonicalCompletedNativeLogDerivativeMoment n : ℂ) := by
        rw [MvPolynomial.coeff_monomial, if_pos hmain]
  · rw [if_neg hab]
    apply Finset.sum_eq_zero
    intro r hr
    have hrle : r ≤ 2*n := by
      have hr' := Finset.mem_range.mp hr
      omega
    have hneq :
        Finsupp.single (0 : Fin 2) (2*n-r) + Finsupp.single (1 : Fin 2) r ≠
          Finsupp.single (0 : Fin 2) a + Finsupp.single (1 : Fin 2) b := by
      intro heq
      exact hab ((nativePhysicalCayleyExponentPair_iff n a b r hrle).mp heq).2
    rw [MvPolynomial.coeff_monomial, if_neg hneq]

/-- The even-even coefficients form the first canonical Hankel tower. -/
theorem nativePhysicalCayleyHomogeneousPolynomial_even_even_coeff
    (i j : ℕ) :
    MvPolynomial.coeff
        (Finsupp.single (0 : Fin 2) (2*i) +
          Finsupp.single (1 : Fin 2) (2*j))
        (nativePhysicalCayleyHomogeneousPolynomial (i+j)) =
      4 * (-1:ℂ)^(i+j) *
        (canonicalCompletedNativeLogDerivativeMoment (i+j) : ℂ) := by
  rw [nativePhysicalCayleyHomogeneousPolynomial_coeff]
  have hdegree : 2*i+2*j=2*(i+j) := by omega
  simp [hdegree, pow_add, pow_mul]

/-- The odd-odd coefficients form the shifted canonical Hankel tower. -/
theorem nativePhysicalCayleyHomogeneousPolynomial_odd_odd_coeff
    (i j : ℕ) :
    MvPolynomial.coeff
        (Finsupp.single (0 : Fin 2) (2*i+1) +
          Finsupp.single (1 : Fin 2) (2*j+1))
        (nativePhysicalCayleyHomogeneousPolynomial (i+j+1)) =
      4 * (-1:ℂ)^(i+j) *
        (canonicalCompletedNativeLogDerivativeMoment (i+j+1) : ℂ) := by
  rw [nativePhysicalCayleyHomogeneousPolynomial_coeff]
  have hdegree : (2*i+1)+(2*j+1)=2*(i+j+1) := by omega
  have hphase : (i+j+1)+(2*j+1)=(i+j)+2*(j+1) := by omega
  simp [hdegree, hphase, pow_add, pow_mul]

/-- Mixed parity coefficients vanish because every homogeneous summand has
even total degree. -/
theorem nativePhysicalCayleyHomogeneousPolynomial_mixed_coeff
    (i j : ℕ) (n : ℕ) :
    MvPolynomial.coeff
        (Finsupp.single (0 : Fin 2) (2*i) +
          Finsupp.single (1 : Fin 2) (2*j+1))
        (nativePhysicalCayleyHomogeneousPolynomial n) = 0 := by
  rw [nativePhysicalCayleyHomogeneousPolynomial_coeff]
  have hdegree : (2*i)+(2*j+1) ≠ 2*n := by omega
  simp [hdegree]

/-- The opposite mixed-parity coefficients vanish as well. -/
theorem nativePhysicalCayleyHomogeneousPolynomial_odd_even_coeff
    (i j : ℕ) (n : ℕ) :
    MvPolynomial.coeff
        (Finsupp.single (0 : Fin 2) (2*i+1) +
          Finsupp.single (1 : Fin 2) (2*j))
        (nativePhysicalCayleyHomogeneousPolynomial n) = 0 := by
  rw [nativePhysicalCayleyHomogeneousPolynomial_coeff]
  have hdegree : (2*i+1)+(2*j) ≠ 2*n := by omega
  simp [hdegree]

/-- Every coefficient outside total degree `2n` vanishes in the nth
homogeneous polynomial. -/
theorem nativePhysicalCayleyHomogeneousPolynomial_coeff_zero_of_degree_ne
    (n a b : ℕ) (hdegree : a+b ≠ 2*n) :
    MvPolynomial.coeff
        (Finsupp.single (0 : Fin 2) a + Finsupp.single (1 : Fin 2) b)
        (nativePhysicalCayleyHomogeneousPolynomial n) = 0 := by
  rw [nativePhysicalCayleyHomogeneousPolynomial_coeff]
  simp [hdegree]

end
end CarryCauchyResidual
