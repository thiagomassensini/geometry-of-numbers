import SigmaZeroObstruction
import CarrySelfAdjointOperator.NativeScalarZetaIdentification
import CarrySelfAdjointOperator.CompletedGreenJetCoefficientRecurrence
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Entire continuation of the native completed characteristic

The native characteristic is only defined analytically on its centered strip. This file
constructs the entire continuation from Mathlib's entire regularized completed zeta and proves
that it has the same values, hence the same germs, as the native characteristic on that strip.
The continuation is a tool for zero isolation; it does not assert any zero-free region.
-/

namespace CarrySigmaObstruction

open CarrySelfAdjointOperator CarrySigmaSource CPFormal.Analytic.Cp Filter Topology

noncomputable section
set_option autoImplicit false

/-- The entire continuation of the native characteristic, written using Mathlib's entire
regularized completed zeta `Λ₀`. The additive `1/2` is forced by
`completedRiemannZeta = Λ₀ - 1/s - 1/(1-s)` and the native normalization
`(1/2) s (s-1) Λ(s)`. -/
def completedNativeCharacteristicContinuation (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) +
    (1 / 2 : ℂ) * operatorHeightParameter z *
      (operatorHeightParameter z - 1) *
        completedRiemannZeta₀ (operatorHeightParameter z)

/-- The continuation is analytic everywhere because `completedRiemannZeta₀` is entire. -/
theorem completedNativeCharacteristicContinuation_analyticAt (z : ℂ) :
    AnalyticAt ℂ completedNativeCharacteristicContinuation z := by
  have hζ : AnalyticAt ℂ completedRiemannZeta₀ (operatorHeightParameter z) :=
    differentiable_completedZeta₀.analyticAt _
  have harg : AnalyticAt ℂ operatorHeightParameter z := by
    unfold operatorHeightParameter
    fun_prop
  have hcomp : AnalyticAt ℂ
      (fun w : ℂ => completedRiemannZeta₀ (operatorHeightParameter w)) z :=
    hζ.comp harg
  unfold completedNativeCharacteristicContinuation
  fun_prop

/-- The entire continuation inherits the functional equation, hence remains even in the
operator height coordinate. -/
theorem completedNativeCharacteristicContinuation_even (z : ℂ) :
    completedNativeCharacteristicContinuation (-z) =
      completedNativeCharacteristicContinuation z := by
  have harg : operatorHeightParameter (-z) = 1 - operatorHeightParameter z := by
    simp [operatorHeightParameter]
    ring
  rw [completedNativeCharacteristicContinuation, completedNativeCharacteristicContinuation,
    harg, completedRiemannZeta₀_one_sub]
  ring

/-- On the native centered strip, the entire continuation agrees pointwise with the original
completed characteristic. This uses the native-to-zeta identification only where it was proved;
outside that strip the continuation is justified by the identity theorem's specified germ. -/
theorem completedNativeCharacteristicContinuation_eq_native
    {z : ℂ} (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    completedNativeCharacteristicContinuation z =
      completedNativeOperatorCharacteristic z := by
  have hs0 : operatorHeightParameter z ≠ 0 := by
    intro hz
    have hr : (operatorHeightParameter z).re = 0 := by
      simpa using congrArg Complex.re hz
    linarith [hs.1]
  have hs1 : operatorHeightParameter z ≠ 1 := by
    intro hz
    have hr : (operatorHeightParameter z).re = 1 := by
      simpa using congrArg Complex.re hz
    linarith [hs.2]
  rw [completedNativeOperatorCharacteristic_eq_completedRiemannZeta hs,
    nativeXiCompletionFactor_mul_riemannZeta_eq_regularizedCompleted hs,
    completedRiemannZeta_eq]
  dsimp [completedNativeCharacteristicContinuation]
  field_simp [hs0, hs1]
  ring

/-- Entire displaced product of the continued characteristic. -/
def completedNativeDisplacedProductContinuation (d : ℝ) (t : ℂ) : ℂ :=
  completedNativeCharacteristicContinuation (t - Complex.I * (d : ℂ)) *
    completedNativeCharacteristicContinuation (t + Complex.I * (d : ℂ))

/-- The continued displaced product is analytic on the whole plane. -/
theorem completedNativeDisplacedProductContinuation_analyticAt (d : ℝ) (t : ℂ) :
    AnalyticAt ℂ (completedNativeDisplacedProductContinuation d) t := by
  have hminus : AnalyticAt ℂ
      (fun z : ℂ => completedNativeCharacteristicContinuation
        (z - Complex.I * (d : ℂ))) t := by
    exact (completedNativeCharacteristicContinuation_analyticAt _).comp
      (analyticAt_id.sub analyticAt_const)
  have hplus : AnalyticAt ℂ
      (fun z : ℂ => completedNativeCharacteristicContinuation
        (z + Complex.I * (d : ℂ))) t := by
    exact (completedNativeCharacteristicContinuation_analyticAt _).comp
      (analyticAt_id.add analyticAt_const)
  change AnalyticAt ℂ
    (fun z : ℂ =>
      completedNativeCharacteristicContinuation (z - Complex.I * (d : ℂ)) *
        completedNativeCharacteristicContinuation (z + Complex.I * (d : ℂ))) t
  exact hminus.mul hplus

/-- The continued displaced product is even in the complex displacement variable. -/
theorem completedNativeDisplacedProductContinuation_even (d : ℝ) (t : ℂ) :
    completedNativeDisplacedProductContinuation d (-t) =
      completedNativeDisplacedProductContinuation d t := by
  unfold completedNativeDisplacedProductContinuation
  have hleft : -t - Complex.I * (d : ℂ) =
      -(t + Complex.I * (d : ℂ)) := by ring
  have hright : -t + Complex.I * (d : ℂ) =
      -(t - Complex.I * (d : ℂ)) := by ring
  rw [hleft, hright, completedNativeCharacteristicContinuation_even,
    completedNativeCharacteristicContinuation_even]
  ring

/-- On any point where both shifts lie in the original native strip, the continuation of the
displaced product is exactly the original product `displacedProductC`. -/
theorem completedNativeDisplacedProductContinuation_eq_native
    (d : ℝ) (t : ℂ)
    (hminus : operatorHeightParameter (t - Complex.I * (d : ℂ)) ∈ genuineCriticalStrip)
    (hplus : operatorHeightParameter (t + Complex.I * (d : ℂ)) ∈ genuineCriticalStrip) :
    completedNativeDisplacedProductContinuation d t = displacedProductC d t := by
  simp [completedNativeDisplacedProductContinuation, displacedProductC,
    completedNativeCharacteristicContinuation_eq_native hminus,
    completedNativeCharacteristicContinuation_eq_native hplus]

/-- The entire product and the original shifted source have the same germ at the center for
every admissible displacement. This is the local provenance bridge needed before applying an
external zero-isolation certificate to the entire continuation. -/
theorem completedNativeDisplacedProductContinuation_eq_native_eventually
    (d : ℝ) (hd₁ : -(1 / 2 : ℝ) < d) (hd₂ : d < (1 / 2 : ℝ)) :
    ∀ᶠ t : ℂ in 𝓝 0,
      completedNativeDisplacedProductContinuation d t = displacedProductC d t := by
  have hminus0 : (0 : ℂ) - Complex.I * (d : ℂ) ∈ completedNativeHeightDomain := by
    show operatorHeightParameter ((0 : ℂ) - Complex.I * (d : ℂ)) ∈ genuineCriticalStrip
    have heq : (0 : ℂ) - Complex.I * (d : ℂ) = displacedHeight d 0 := by
      simp [displacedHeight]
    rw [heq]
    exact displacedHeight_strip d 0 hd₁ hd₂
  have hplus0 : (0 : ℂ) + Complex.I * (d : ℂ) ∈ completedNativeHeightDomain := by
    show operatorHeightParameter ((0 : ℂ) + Complex.I * (d : ℂ)) ∈ genuineCriticalStrip
    have heq : (0 : ℂ) + Complex.I * (d : ℂ) = displacedHeight (-d) 0 := by
      simp [displacedHeight]
    rw [heq]
    exact displacedHeight_strip (-d) 0 (by linarith) (by linarith)
  have hminusTendsto : Tendsto
      (fun t : ℂ => t - Complex.I * (d : ℂ)) (𝓝 0)
      (𝓝 ((0 : ℂ) - Complex.I * (d : ℂ))) := by
    change Tendsto (id - fun _ : ℂ => Complex.I * (d : ℂ)) (𝓝 0)
      (𝓝 (0 - Complex.I * (d : ℂ)))
    exact (continuousAt_id.sub continuousAt_const).tendsto
  have hplusTendsto : Tendsto
      (fun t : ℂ => t + Complex.I * (d : ℂ)) (𝓝 0)
      (𝓝 ((0 : ℂ) + Complex.I * (d : ℂ))) := by
    change Tendsto (id + fun _ : ℂ => Complex.I * (d : ℂ)) (𝓝 0)
      (𝓝 (0 + Complex.I * (d : ℂ)))
    exact (continuousAt_id.add continuousAt_const).tendsto
  have hminus := hminusTendsto.eventually
    (isOpen_completedNativeHeightDomain.mem_nhds hminus0)
  have hplus := hplusTendsto.eventually
    (isOpen_completedNativeHeightDomain.mem_nhds hplus0)
  filter_upwards [hminus, hplus] with t hminus hplus
  apply completedNativeDisplacedProductContinuation_eq_native d t
  · simpa [completedNativeHeightDomain] using hminus
  · simpa [completedNativeHeightDomain] using hplus

end
end CarrySigmaObstruction

#print axioms CarrySigmaObstruction.completedNativeCharacteristicContinuation_analyticAt
#print axioms CarrySigmaObstruction.completedNativeCharacteristicContinuation_even
#print axioms CarrySigmaObstruction.completedNativeCharacteristicContinuation_eq_native
#print axioms CarrySigmaObstruction.completedNativeDisplacedProductContinuation_even
#print axioms CarrySigmaObstruction.completedNativeDisplacedProductContinuation_eq_native_eventually
