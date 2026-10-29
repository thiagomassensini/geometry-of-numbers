import RadialReality
import NativeEulerTransport
import CarrySelfAdjointOperator.NativePhysicalFiniteSewing

namespace CarryMovingRadial
open CarrySelfAdjointOperator CarrySelfAdjointOperator.PhysicalSewing
open CarrySelfAdjointOperator.ChiralReturn NativeLaguerre
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000

def point (h : ℝ) (r : ℕ) : ℂ := Complex.I*((r:ℂ)+1)*(h:ℂ)
def scale (h : ℝ) : ℂ := (Real.sqrt h⁻¹:ℂ)

/-- Extension of the EXISTING projective transform in its original carrier.
No metric or source amplitude is changed. Equality on the native grid is below. -/
def curveState (N : ℕ) (h : ℝ) (x : Fin N → ℂ) :
    CanonicalCompletedNativeProjectiveChiralCarrier :=
  ∑ r : Fin N, x r • canonicalCompletedNativeProjectiveChiralTransform (point h r)
    (scale h • completedNativeChiralCauchyFeature r)

theorem point_at_grid (k r : ℕ) : point (radialFourSourceStep k) r=
    canonicalCompletedC3RadialTiltPoint k r := by
  norm_num [point,radialFourSourceStep,canonicalCompletedC3RadialTiltPoint,
    canonicalCompletedC3RadialTiltStep,canonicalGreenJetStep]
  ring

theorem scale_at_grid (k : ℕ) : scale (radialFourSourceStep k)=
    (Real.sqrt ((k:ℝ)+1):ℂ) := by
  simp [scale,radialFourSourceStep]

/-- BOTH physical legs, with precisely ONE original projective amplitude. -/
theorem curve_at_grid (N k : ℕ) (x : Fin N → ℂ) :
    curveState N (radialFourSourceStep k) x=finiteProjectiveSource N k x := by
  unfold curveState finiteProjectiveSource
  apply Finset.sum_congr rfl
  intro r _
  rw [point_at_grid,scale_at_grid]
  rw [canonicalCompletedNativeRadialProjectiveChiralState_eq_transform]
  rfl

theorem curve_eq_original (N k : ℕ) (x : Fin N → ℂ) :
    curveState N (radialFourSourceStep k) x=
      physicalCompletedFiniteSource k (finRadialCoefficients N x) := by
  rw [curve_at_grid,physicalCompletedFiniteSource_fin]


theorem finite_coefficients_support (N : ℕ) (x : Fin N → ℂ) :
    (finRadialCoefficients N x).support⊆Finset.range N := by
  intro j hj
  by_contra hn
  have hn' : N≤j := Nat.le_of_not_lt (fun h => hn (Finset.mem_range.mpr h))
  exact (Finsupp.mem_support_iff.mp hj) (finRadialCoefficients_outside N x j hn')

/-- Compatibility with the EXISTING all-order physical Euler/Newton chart,
with the same completed source rather than a separately chosen Gram family. -/
theorem curve_euler_newton (n k : ℕ) (x : Fin (2*n) → ℂ)
    (hF : ∀ i : Fin (2*n), completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i)≠0)
    (hP : ∀ i : Fin (2*n), completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i)≠0) :
    curveState (2*n) (radialFourSourceStep k) x=
      nativeSourceProjectiveBoundaryJetSynthesis n k
        (CarryEulerNewtonAll.eulerNewton (2*n) (radialFourSourceStep k)
          (CarryEulerNewtonAll.physicalEulerChart n k (finRadialCoefficients (2*n) x))) := by
  rw [curve_eq_original]
  exact CarryEulerNewtonAll.physical_source_euler_all_order n k _
    (finite_coefficients_support (2*n) x) hF hP

def fixedSynthesis (N : ℕ) (c : Fin N → ℂ) : CanonicalCompletedNativeChiralCauchyCarrier :=
  ∑ r : Fin N, c r • completedNativeChiralCauchyFeature r

def curveCoefficients (N : ℕ) (h : ℝ) (x : Fin N → ℂ) : Fin N → ℂ := fun r =>
  scale h*completedNativeNormalizedPositiveChiralAmplitude (point h r)*x r

def curveQuotient (h : ℝ) (r : ℕ) : ℂ :=
  completedNativeHermiteBiehlerChiralQuotient (point h r)

theorem curve_legs (N : ℕ) (h : ℝ) (x : Fin N → ℂ) :
    curveState N h x=(fixedSynthesis N (curveCoefficients N h x),
      fixedSynthesis N (fun r => curveCoefficients N h x r*curveQuotient h r)) := by
  apply Prod.ext
  all_goals simp only [curveState,Prod.fst_sum,Prod.snd_sum,Prod.smul_fst,Prod.smul_snd,
    canonicalCompletedNativeProjectiveChiralTransform,LinearMap.coe_mk,AddHom.coe_mk,
    smul_smul,fixedSynthesis,curveCoefficients,curveQuotient]
  all_goals apply Finset.sum_congr rfl
  all_goals intro r _; congr 1; ring

/-- Exact cancellation imposed by the EXISTING completion normalization. -/
theorem original_amplitude (z : ℂ) (hF : completedNativeOperatorCharacteristic z≠0) :
    completedNativeNormalizedPositiveChiralAmplitude z=
      (completedNativeOperatorLogDerivative z+Complex.I)/(Real.sqrt 2:ℂ) := by
  have hs : (Real.sqrt 2:ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne'
  unfold completedNativeNormalizedPositiveChiralAmplitude
    canonicalCompletedC3FullWronskianChiralNormalization
    completedNativePositiveHermiteBiehlerCoordinate completedNativeOperatorLogDerivative
  field_simp [hF,hs]

theorem original_returned_amplitude (z : ℂ)
    (hF : completedNativeOperatorCharacteristic z≠0)
    (hP : completedNativePositiveHermiteBiehlerCoordinate z≠0) :
    completedNativeNormalizedPositiveChiralAmplitude z*
        completedNativeHermiteBiehlerChiralQuotient z=
      (completedNativeOperatorLogDerivative z-Complex.I)/(Real.sqrt 2:ℂ) := by
  have hs : (Real.sqrt 2:ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne'
  unfold completedNativeNormalizedPositiveChiralAmplitude
    canonicalCompletedC3FullWronskianChiralNormalization
    completedNativeHermiteBiehlerChiralQuotient
  have he : completedNativePositiveHermiteBiehlerCoordinate z*
      (completedNativeNegativeHermiteBiehlerCoordinate z/completedNativePositiveHermiteBiehlerCoordinate z)=
        completedNativeNegativeHermiteBiehlerCoordinate z := by field_simp [hP]
  rw [mul_assoc,he]
  unfold completedNativeNegativeHermiteBiehlerCoordinate completedNativeOperatorLogDerivative
  field_simp [hF,hs]

end
end CarryMovingRadial
