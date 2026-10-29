import Stencil
import BoundaryOperator
import CarrySelfAdjointOperator.NativeGeometricLogClock

namespace CarryStencilBoundary
open CarrySelfAdjointOperator NativeLaguerre CarryNativeTfvd CarryCriticalTfvd
open CarryCurvatureGreen CarryLinearTfvd
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

/-- Repeated-complement lift of the ACTUAL jet coefficient, including its phase. -/
def nativeLift (k n : ℕ) : PhysicalSpace :=
  (-2*radialLeadingScalar k (n+2)) •
    ((physicalComplement^n) (completedNativeChiralCauchyFeature 0))

/-- Boundary forced by the original two traces and the calibrated P_n. -/
def nativeBoundary (k n : ℕ) : PhysicalSpace :=
  radialLeadingScalar k (n+2) • physicalRadialAdvance
    (boundaryOperator n (completedNativeChiralCauchyFeature 0))

theorem native_lift_curvature (k n : ℕ) :
    physicalCurvature (nativeLift k n)=physicalCauchySynthesis (radialJetCoefficients k (n+2)) := by
  rw [radial_jet_synthesis]
  simp only [physicalCurvature, nativeLift, map_smul, smul_smul]
  simp only [pow_succ', mul_apply_eq_comp]
  congr 1
  ring

/-- All orders m=n+2: exact whole-vector tangent defect with the original
radial factorial, phase, two traces, and exterior coefficient halo. -/
theorem native_tangent_boundary (eta : ℝ) (k n : ℕ) :
    physicalCauchySynthesis
      (completionCommutator eta (monomialWeight 1) (radialJetCoefficients k (n+2))) =
      physicalTangent eta (nativeLift k n)+(eta : ℂ)⁻¹ • nativeBoundary k n := by
  apply physicalRadialAdvance_injective
  rw [physical_linear_numerator]
  have hb := congrArg (fun T : PhysicalSpace →L[ℂ] PhysicalSpace =>
    T (completedNativeChiralCauchyFeature 0)) (boundary_operator_identity n)
  simp only [mul_apply_eq_comp, sub_apply, add_apply, one_apply_eq_self,
    smul_apply, pow_two, physicalRadialAdvance_feature] at hb
  rw [physicalTangent, native_lift_curvature]
  simp only [nativeBoundary, map_add, map_smul, map_sub,
    radial_jet_synthesis, physicalTrace,
    (radial_jet_two_traces k (n+2)).1, (radial_jet_two_traces k (n+2)).2,
    nativeLift, smul_smul]
  rw [hb]
  module

theorem advance_complement_power (m : ℕ) (f : PhysicalSpace) :
    physicalRadialAdvance ((physicalComplement^m) f)=
      (physicalComplement^m) (physicalRadialAdvance f) := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [pow_succ', mul_apply_eq_comp]
    rw [advance_complement, ih]

theorem resolvent_complement_power (m : ℕ) (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (f : PhysicalSpace) :
    physicalGreenResolvent eta h0.le h1 ((physicalComplement^m) f)=
      (physicalComplement^m) (physicalGreenResolvent eta h0.le h1 f) := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [pow_succ', mul_apply_eq_comp]
    rw [resolvent_complement eta h0 h1, ih]

/-- Two independent physical inputs, before taking Re or identifying them. -/
theorem boundary_polarized_factor (m n : ℕ) (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (f g : PhysicalSpace) :
    inner ℂ ((physicalComplement^m) f)
      (physicalGreenOperator eta h0.le h1 (physicalRadialAdvance (boundaryOperator n g))) =
      (eta : ℂ)*inner ℂ (baseGradient eta h0 h1 f)
        ((physicalComplement^m*boundaryOperator n) (baseGradient eta h0 h1 g)) := by
  rw [green_inner_transport eta h0 h1, advance_complement_power,
    resolvent_complement_power m eta h0 h1, boundary_advance,
    boundary_resolvent n eta h0 h1]
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (physical_complement_selfAdjoint.pow m)
  change (eta : ℂ)*inner ℂ ((physicalComplement^m) (baseGradient eta h0 h1 f))
    (boundaryOperator n (baseGradient eta h0 h1 g)) = _
  have hh := hs (baseGradient eta h0 h1 f) (boundaryOperator n (baseGradient eta h0 h1 g))
  change inner ℂ ((physicalComplement^m) (baseGradient eta h0 h1 f))
    (boundaryOperator n (baseGradient eta h0 h1 g)) =
      inner ℂ (baseGradient eta h0 h1 f)
        ((physicalComplement^m) (boundaryOperator n (baseGradient eta h0 h1 g))) at hh
  exact congrArg (fun z : ℂ => (eta : ℂ)*z) hh

theorem boundary_pair_nonnegative (m n : ℕ) (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (f : PhysicalSpace) :
    0 ≤ (inner ℂ ((physicalComplement^m) f)
      (physicalGreenOperator eta h0.le h1 (physicalRadialAdvance (boundaryOperator n f)))).re := by
  rw [boundary_polarized_factor m n eta h0 h1]
  have hp := (boundary_product_positive m n).re_inner_nonneg_right (baseGradient eta h0 h1 f)
  change 0 ≤ (inner ℂ (baseGradient eta h0 h1 f)
    ((physicalComplement^m*boundaryOperator n) (baseGradient eta h0 h1 f))).re at hp
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    using mul_nonneg h0.le hp

/-- A sign for the actual all-order native boundary, including the original
complex phase. It is not a sign assumption on any canonical moment. -/
theorem native_boundary_pair_nonnegative (k n : ℕ) (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    0 ≤ (inner ℂ (physicalCauchySynthesis (radialJetCoefficients k (n+2)))
      (physicalGreenOperator eta h0.le h1 (nativeBoundary k n))).re := by
  have hp := boundary_pair_nonnegative (n+2) n eta h0 h1
    (radialLeadingScalar k (n+2) • completedNativeChiralCauchyFeature 0)
  simpa only [radial_jet_synthesis, nativeBoundary, map_smul] using hp

/-- All m=n+2 have a nonnegative SPATIAL LINEAR commutator coefficient.
This is not the nonlinear completed Schur residual or a Hankel Gram. -/
theorem native_linear_coefficient_nonnegative (k n : ℕ) (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    0 ≤ (inner ℂ (physicalCauchySynthesis (radialJetCoefficients k (n+2)))
      (physicalGreenOperator eta h0.le h1 (physicalCauchySynthesis
        (completionCommutator eta (monomialWeight 1) (radialJetCoefficients k (n+2)))))).re := by
  have hp := native_boundary_pair_nonnegative k n eta h0 h1
  have hc := curvature_green_nonnegative eta h0 h1 (nativeLift k n)
  rw [native_lift_curvature] at hc
  rw [native_tangent_boundary]
  simp only [map_add, map_smul, inner_add_right, inner_smul_right, Complex.add_re,
    Complex.mul_re, ← Complex.ofReal_inv, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  exact add_nonneg hc (mul_nonneg (inv_nonneg.mpr h0.le) hp)

end
end CarryStencilBoundary
