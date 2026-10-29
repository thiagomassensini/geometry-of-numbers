import CarrySelfAdjointOperator.NativePhysicalGreenResolvent

namespace CarryQuarticBoundary
noncomputable section
set_option autoImplicit false

/-- Candidate boundary polynomial from the finite TFVD defect. The index n
corresponds to difference order n+2, not to carry depth or a moment index. -/
def boundaryPolynomial : ℕ → ℝ → ℝ
  | 0, _ => 0
  | n+1, x => (n+2 : ℕ) + x*boundaryPolynomial n x

/-- Exact finite geometric cancellation in arbitrary order, independent of
any moment sign. Native operator calibration beyond order four is separate. -/
theorem boundary_polynomial_identity (n : ℕ) (x : ℝ) :
    (1-x)^2*boundaryPolynomial n x =
      (n+1 : ℕ) - ((n+2 : ℕ) : ℝ)*x - x^n + 2*x^(n+1) := by
  induction n with
  | zero => simp [boundaryPolynomial]
  | succ n ih =>
    rw [boundaryPolynomial]
    calc
      _ = ((n+2 : ℕ) : ℝ)*(1-x)^2+x*((1-x)^2*boundaryPolynomial n x) := by ring
      _ = _ := by rw [ih]; push_cast; simp only [pow_succ]; ring

theorem boundary_polynomial_nonnegative (n : ℕ) (x : ℝ) (hx : 0≤x) :
    0 ≤ boundaryPolynomial n x := by
  induction n with
  | zero => simp [boundaryPolynomial]
  | succ n ih =>
    change 0 ≤ ((n+2 : ℕ) : ℝ)+x*boundaryPolynomial n x
    positivity

theorem boundary_polynomial_lower (n : ℕ) (x : ℝ) (hx : 0≤x) :
    ((n+2 : ℕ) : ℝ) ≤ boundaryPolynomial (n+1) x := by
  change ((n+2 : ℕ) : ℝ) ≤ ((n+2 : ℕ) : ℝ)+x*boundaryPolynomial n x
  have hh := mul_nonneg hx (boundary_polynomial_nonnegative n x hx)
  linarith

theorem boundary_polynomial_two (x : ℝ) : boundaryPolynomial 2 x=3+2*x := by
  norm_num [boundaryPolynomial]
  ring

theorem boundary_polynomial_in_native_coordinate (n : ℕ) (u : ℝ) :
    u^2*boundaryPolynomial n (1-u)=
      (1-u)^n*(1-2*u)-1+((n+2 : ℕ) : ℝ)*u := by
  have hh := boundary_polynomial_identity n (1-u)
  simp only [sub_sub_cancel] at hh
  rw [hh]
  rw [pow_succ]
  push_cast
  ring

end
end CarryQuarticBoundary
