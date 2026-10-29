import CarrySelfAdjointOperator.CompletedNativeChiralJetStorageTransport
import Mathlib.Tactic

/-! Leading asymptotics of BOTH original source channels. Rescaling below
is used only to observe a limit of the original vectors; it does not change
the source, metric, synthesis, or return operator. -/
namespace CarryCriticalRelative
open CarrySelfAdjointOperator CarrySelfAdjointOperator.ChiralReturn
open Filter Topology
open scoped BigOperators InnerProductSpace
noncomputable section
set_option maxHeartbeats 1200000

abbrev amp := completedNativeNormalizedPositiveChiralAmplitude
abbrev step := canonicalCompletedC3RadialSecondStep

theorem amp_continuousAt_zero : ContinuousAt amp 0 := by
  have hF := completedNativeOperatorCharacteristic_analyticAt zero_mem_completedNativeHeightDomain
  have hden : (Real.sqrt 2 : ℂ) * completedNativeOperatorCharacteristic 0 ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)).ne')
      completedNativeOperatorCharacteristic_zero_ne_zero
  unfold amp completedNativeNormalizedPositiveChiralAmplitude
    canonicalCompletedC3FullWronskianChiralNormalization
  exact ((continuousAt_const.mul hF.continuousAt).inv₀ hden).mul
    (hF.deriv.neg.continuousAt.add (continuousAt_const.mul hF.continuousAt))

theorem amp_zero_ne : amp 0 ≠ 0 :=
  completedNativeNormalizedPositiveChiralAmplitude_ne_zero
    completedNativeOperatorCharacteristic_zero_ne_zero (by
      rw [completedNativePositiveHermiteBiehlerCoordinate_zero]
      exact mul_ne_zero Complex.I_ne_zero completedNativeOperatorCharacteristic_zero_ne_zero)

theorem amp_tendsto (r : ℕ) :
    Tendsto (fun k => amp (canonicalCompletedC3RadialTiltPoint k r)) atTop (nhds (amp 0)) :=
  amp_continuousAt_zero.tendsto.comp (canonicalCompletedC3RadialTiltPoint_tendsto_zero r)

theorem quotient_tendsto (r : ℕ) :
    Tendsto (fun k => completedNativeHermiteBiehlerChiralQuotient
      (canonicalCompletedC3RadialTiltPoint k r)) atTop (nhds (-1)) := by
  have h := hasDerivAt_completedNativeHermiteBiehlerChiralQuotient_zero_raw.continuousAt.tendsto.comp
    (canonicalCompletedC3RadialTiltPoint_tendsto_zero r)
  simpa only [Function.comp_def, completedNativeHermiteBiehlerChiralQuotient_zero] using h

theorem step_factor (k m a : ℕ) (ha : a ≤ m) :
    step k ^ m * (((a.factorial : ℂ) * step k ^ a)⁻¹) =
      (a.factorial : ℂ)⁻¹ * step k ^ (m-a) := by
  have hs := canonicalCompletedC3RadialSecondStep_ne_zero k
  have hf : (a.factorial : ℂ) ≠ 0 := by exact_mod_cast a.factorial_ne_zero
  rw [show m = (m-a)+a by omega, pow_add]
  field_simp
  simp only [Nat.add_sub_cancel]

theorem step_pow_inputMatrix (n k m : ℕ) (r a : Fin (2*n)) (ha : a.val ≤ m) :
    step k ^ m * nativeSourceChiralJetInputMatrix n k r a =
      amp (canonicalCompletedC3RadialTiltPoint k r) * nativeSourceJetOrderPhase a *
        (a.val.factorial : ℂ)⁻¹ * step k ^ (m-a.val) * completedGreenForwardWeight a r := by
  unfold nativeSourceChiralJetInputMatrix
  have h := step_factor k m a ha
  linear_combination (norm := ring_nf) h *
    (amp (canonicalCompletedC3RadialTiltPoint k r) * nativeSourceJetOrderPhase a *
      completedGreenForwardWeight a r)

def leadingCoefficients (n m : ℕ) (x : Fin (2*n) → ℂ) (hm : m < 2*n) : Fin (2*n) → ℂ :=
  fun r => amp 0 * nativeSourceJetOrderPhase m * (m.factorial : ℂ)⁻¹ *
    completedGreenForwardWeight m r * x ⟨m,hm⟩

theorem scaled_input_tendsto (n m : ℕ) (x : Fin (2*n) → ℂ) (hm : m < 2*n)
    (hx : ∀ a : Fin (2*n), m < a.val → x a = 0) :
    Tendsto (fun k => fun r => step k ^ m * nativeSourceChiralJetInput n k x r)
      atTop (nhds (leadingCoefficients n m x hm)) := by
  apply tendsto_pi_nhds.mpr
  intro r
  have ht (a : Fin (2*n)) :
      Tendsto (fun k => step k ^ m * nativeSourceChiralJetInputMatrix n k r a * x a)
        atTop (nhds (if a.val = m then leadingCoefficients n m x hm r else 0)) := by
    by_cases ham : a.val ≤ m
    · simp_rw [step_pow_inputMatrix n _ m r a ham]
      have hs := canonicalCompletedC3RadialSecondStep_tendsto_zero.pow (m-a.val)
      have h := (((((amp_tendsto r).mul_const (nativeSourceJetOrderPhase a)).mul_const
        ((a.val.factorial : ℂ)⁻¹)).mul hs).mul_const
          (completedGreenForwardWeight a r)).mul_const (x a)
      by_cases he : a.val = m
      · have hea : a = ⟨m,hm⟩ := Fin.ext he
        simpa [he, hea, leadingCoefficients] using h
      · simpa [he, Nat.sub_ne_zero_iff_lt.mpr (by omega : a.val < m)] using h
    · have hz := hx a (by omega)
      simp only [hz, mul_zero]
      have he : a.val ≠ m := by omega
      simpa only [if_neg he] using (tendsto_const_nhds (x := (0:ℂ)))
  have hsum := tendsto_finsetSum Finset.univ (fun a _ => ht a)
  have he : (∑ a : Fin (2*n), if a.val = m then leadingCoefficients n m x hm r else 0) =
      leadingCoefficients n m x hm r := by
    rw [Finset.sum_eq_single (⟨m,hm⟩ : Fin (2*n))]
    · simp
    · intro a _ hne
      rw [if_neg (by intro he; exact hne (Fin.ext he))]
    · simp
  rw [he] at hsum
  simpa only [nativeSourceChiralJetInput, LinearMap.coe_mk, AddHom.coe_mk, Finset.mul_sum,
    mul_assoc] using hsum

def leadingState (n m : ℕ) (x : Fin (2*n) → ℂ) (hm : m < 2*n) :
    CanonicalCompletedNativeChiralCauchyCarrier :=
  radialIncidentSynthesis 0 (2*n) (leadingCoefficients n m x hm)

theorem leadingState_ne_zero (n m : ℕ) (x : Fin (2*n) → ℂ) (hm : m < 2*n)
    (hxm : x ⟨m,hm⟩ ≠ 0) : leadingState n m x hm ≠ 0 := by
  intro hz
  have hc : leadingCoefficients n m x hm = 0 := by
    apply (radialIncidentSynthesis_injective 0 (2*n))
    simpa [leadingState] using hz
  have ht := congrFun hc (⟨m,hm⟩ : Fin (2*n))
  have hp : nativeSourceJetOrderPhase m ≠ 0 := by
    unfold nativeSourceJetOrderPhase
    exact_mod_cast pow_ne_zero (m/2) (by norm_num : (-1:ℝ) ≠ 0)
  have hf : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  have hw : completedGreenForwardWeight m m = 1 := by
    norm_num [completedGreenForwardWeight]
  simp only [leadingCoefficients, hw, mul_one, Pi.zero_apply] at ht
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero amp_zero_ne hp) (inv_ne_zero hf)) hxm) ht

end
end CarryCriticalRelative
