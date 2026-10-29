import BoundaryPolynomial
import CurvatureKernel

namespace CarryStencilBoundary
open CarrySelfAdjointOperator NativeLaguerre CarryCurvatureGreen CarryQuarticBoundary
open scoped unitInterval InnerProductSpace
noncomputable section
set_option autoImplicit false

/-- The old scalar boundary polynomial evaluated in the ORIGINAL coordinate.
The recurrence fixes every coefficient; no source or metric is fitted. -/
def boundarySymbol : ℕ → C(unitInterval, ℂ)
  | 0 => 0
  | n+1 => ((n+2 : ℕ) : ℂ) • 1 +
      (1-physicalRadialCoefficient)*boundarySymbol n

def boundaryOperator (n : ℕ) : PhysicalSpace →L[ℂ] PhysicalSpace :=
  intervalMultiplier (boundarySymbol n)

theorem boundary_symbol_eval (n : ℕ) (u : unitInterval) :
    boundarySymbol n u = (boundaryPolynomial n (1-(u : ℝ)) : ℝ) := by
  induction n with
  | zero => simp [boundarySymbol, boundaryPolynomial]
  | succ n ih =>
    simp only [boundarySymbol, ContinuousMap.add_apply, ContinuousMap.smul_apply,
      ContinuousMap.one_apply, ContinuousMap.mul_apply, ContinuousMap.sub_apply,
      physicalRadialCoefficient, ContinuousMap.coe_mk, smul_eq_mul, mul_one, ih,
      boundaryPolynomial]
    push_cast
    rfl

theorem multiplier_add (m n : C(unitInterval, ℂ)) :
    intervalMultiplier (m+n)=intervalMultiplier m+intervalMultiplier n := by
  have he : m+n=m-(-1 : ℂ) • n := by module
  rw [he, intervalMultiplier_sub, intervalMultiplier_smul]
  simp

theorem multiplier_zero : intervalMultiplier (0 : C(unitInterval, ℂ))=0 := by
  rw [show (0 : C(unitInterval, ℂ))=(0 : ℂ) • 1 by ext; simp]
  rw [intervalMultiplier_smul, zero_smul]

theorem multiplier_pow (m : C(unitInterval, ℂ)) (n : ℕ) :
    intervalMultiplier (m^n)=(intervalMultiplier m)^n := by
  induction n with
  | zero => exact intervalMultiplier_one
  | succ n ih => rw [pow_succ, intervalMultiplier_mul, ih, pow_succ]

theorem complement_multiplier :
    intervalMultiplier (1-physicalRadialCoefficient)=physicalComplement := by
  rw [intervalMultiplier_sub, intervalMultiplier_one]
  rfl

theorem boundary_operator_zero : boundaryOperator 0=0 := by
  exact multiplier_zero

theorem boundary_operator_succ (n : ℕ) :
    boundaryOperator (n+1)=((n+2 : ℕ) : ℂ) • 1+physicalComplement*boundaryOperator n := by
  simp only [boundaryOperator, boundarySymbol, multiplier_add, intervalMultiplier_smul,
    intervalMultiplier_one, intervalMultiplier_mul, complement_multiplier]

/-- Operator calibration of the exact scalar identity from PR97. -/
theorem boundary_operator_identity (n : ℕ) :
    physicalRadialAdvance^2*boundaryOperator n =
      physicalComplement^(n+2)-1+((n+2 : ℕ) : ℂ) • physicalRadialAdvance -
        physicalRadialAdvance^2*physicalComplement^n := by
  have hsymbol : physicalRadialCoefficient^2*boundarySymbol n =
      (1-physicalRadialCoefficient)^(n+2)-1+
        ((n+2 : ℕ) : ℂ) • physicalRadialCoefficient -
        physicalRadialCoefficient^2*(1-physicalRadialCoefficient)^n := by
    ext u
    have hr : (u : ℝ)^2*boundaryPolynomial n (1-(u : ℝ))=
        (1-(u : ℝ))^(n+2)-1+((n+2 : ℕ) : ℝ)*(u : ℝ)-
          (u : ℝ)^2*(1-(u : ℝ))^n := by
      rw [boundary_polynomial_in_native_coordinate]
      simp only [pow_add, pow_two]
      ring
    have hc := congrArg (fun x : ℝ => (x : ℂ)) hr
    push_cast at hc
    simpa only [ContinuousMap.mul_apply, ContinuousMap.pow_apply,
      ContinuousMap.sub_apply, ContinuousMap.add_apply, ContinuousMap.smul_apply,
      ContinuousMap.one_apply, physicalRadialCoefficient, ContinuousMap.coe_mk,
      smul_eq_mul, boundary_symbol_eval, Nat.cast_add, Nat.cast_ofNat] using hc
  have hi := congrArg intervalMultiplier hsymbol
  simpa only [intervalMultiplier_mul, multiplier_pow, multiplier_add,
    intervalMultiplier_sub, intervalMultiplier_one, intervalMultiplier_smul,
    complement_multiplier, physicalRadialAdvance, physicalComplement, boundaryOperator] using hi

/-- Positivity follows from the pre-existing scalar P, on the original L². -/
theorem boundary_operator_positive (n : ℕ) : (boundaryOperator n).IsPositive := by
  apply intervalMultiplier_isPositive
  · intro u
    rw [boundary_symbol_eval]
    simp
  · intro u
    rw [boundary_symbol_eval]
    simp only [Complex.ofReal_re]
    exact boundary_polynomial_nonnegative n _ (sub_nonneg.mpr u.property.2)

theorem boundary_operator_lower_positive (n : ℕ) :
    (boundaryOperator (n+1)-((n+2 : ℕ) : ℂ) • 1).IsPositive := by
  have he : boundaryOperator (n+1)-((n+2 : ℕ) : ℂ) • 1 =
      intervalMultiplier (boundarySymbol (n+1)-((n+2 : ℕ) : ℂ) • 1) := by
    rw [intervalMultiplier_sub, intervalMultiplier_smul, intervalMultiplier_one]
    rfl
  rw [he]
  apply intervalMultiplier_isPositive
  · intro u
    simp only [ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.one_apply,
      smul_eq_mul, mul_one, boundary_symbol_eval]
    simp
  · intro u
    simp only [ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.one_apply,
      smul_eq_mul, mul_one, boundary_symbol_eval, Complex.sub_re, Complex.ofReal_re,
      Complex.natCast_re]
    exact sub_nonneg.mpr (boundary_polynomial_lower n _ (sub_nonneg.mpr u.property.2))

theorem boundary_operator_lower (n : ℕ) (f : PhysicalSpace) :
    ((n+2 : ℕ) : ℝ)*‖f‖^2 ≤ (inner ℂ f (boundaryOperator (n+1) f)).re := by
  have hh := (boundary_operator_lower_positive n).re_inner_nonneg_right f
  change 0 ≤ (inner ℂ f ((boundaryOperator (n+1)-((n+2 : ℕ) : ℂ) • 1) f)).re at hh
  simp only [sub_apply, smul_apply, one_apply_eq_self, inner_sub_right,
    inner_smul_right, inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal] at hh
  have hRe (r : ℝ) : ((r : ℂ)^2).re=r^2 := by simp [pow_two, Complex.mul_re]
  norm_num [Complex.sub_re, Complex.mul_re, hRe] at hh
  simpa only [Nat.cast_add, Nat.cast_ofNat] using hh

theorem multiplier_commute (m n : C(unitInterval, ℂ)) :
    Commute (intervalMultiplier m) (intervalMultiplier n) := by
  show intervalMultiplier m*intervalMultiplier n=intervalMultiplier n*intervalMultiplier m
  rw [← intervalMultiplier_mul, ← intervalMultiplier_mul, mul_comm]

theorem boundary_advance (n : ℕ) (f : PhysicalSpace) :
    physicalRadialAdvance (boundaryOperator n f)=boundaryOperator n (physicalRadialAdvance f) := by
  exact congrArg (fun T : PhysicalSpace →L[ℂ] PhysicalSpace => T f)
    (multiplier_commute physicalRadialCoefficient (boundarySymbol n)).eq

theorem boundary_resolvent (n : ℕ) (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (f : PhysicalSpace) :
    physicalGreenResolvent eta h0.le h1 (boundaryOperator n f)=
      boundaryOperator n (physicalGreenResolvent eta h0.le h1 f) := by
  exact congrArg (fun T : PhysicalSpace →L[ℂ] PhysicalSpace => T f)
    (multiplier_commute (physicalResolventCoefficient eta h0.le h1) (boundarySymbol n)).eq

/-- The product has the nonnegative symbol (1-u)^m P_n(1-u), in the same
metric and on the entire original physical carrier. -/
theorem boundary_product_positive (m n : ℕ) :
    (physicalComplement^m*boundaryOperator n).IsPositive := by
  rw [← complement_multiplier, ← multiplier_pow, boundaryOperator, ← intervalMultiplier_mul]
  have he (u : unitInterval) :
      ((1-physicalRadialCoefficient)^m*boundarySymbol n) u =
        (((1-(u : ℝ))^m*boundaryPolynomial n (1-(u : ℝ)) : ℝ) : ℂ) := by
    simp only [ContinuousMap.mul_apply, ContinuousMap.pow_apply, ContinuousMap.sub_apply,
      ContinuousMap.one_apply, physicalRadialCoefficient, ContinuousMap.coe_mk,
      boundary_symbol_eval]
    push_cast
    rfl
  apply intervalMultiplier_isPositive
  · intro u
    simp only [he, Complex.ofReal_re]
  · intro u
    rw [he]
    simp only [Complex.ofReal_re]
    exact mul_nonneg (pow_nonneg (sub_nonneg.mpr u.property.2) m)
      (boundary_polynomial_nonnegative n _ (sub_nonneg.mpr u.property.2))

end
end CarryStencilBoundary
