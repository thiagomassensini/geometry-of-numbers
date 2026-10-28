import CriticalPhysicalBridge
import CriticalOddSign

namespace CarryMovingRadial
open CarrySelfAdjointOperator NativeLaguerre CarrySelfAdjointOperator.PhysicalSewing
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem critical_weight_real (a h : ℝ) (i : Fin 4) :
    conj (criticalWeight a (h:ℂ) i)=criticalWeight a (h:ℂ) i := by
  fin_cases i <;> norm_num [criticalWeight,map_sub,map_mul,map_pow,map_ofNat]

theorem critical_raw_product (a h : ℝ) (i j : Fin 4) :
    conj (criticalRaw a (h:ℂ) i)*criticalRaw a (h:ℂ) j=
      criticalWeight a (h:ℂ) i*criticalWeight a (h:ℂ) j/(36*(h:ℂ)^6) := by
  unfold criticalRaw
  simp only [map_mul,map_div₀,map_pow,map_ofNat,Complex.conj_I,Complex.conj_ofReal,
    critical_weight_real]
  ring_nf
  norm_num [Complex.I_sq]

/-- Scalar response is identified ONLY after the full state and all crosses.
This is the SAME raw critical source, with its scale and phase preserved. -/
theorem critical_response_energy (a h : ℝ) (hh : h≠0) :
    responsePair 4 h (criticalRaw a (h:ℂ)) (criticalRaw a (h:ℂ))=criticalEnergy a (h:ℂ) := by
  unfold responsePair criticalEnergy criticalKernel
  simp_rw [critical_raw_product]
  rw [Finset.sum_div]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_div,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hq (r : Fin 4) : completedNativeOperatorLogDerivative (Complex.I*((r:ℂ)+1)*(h:ℂ))=
      2*Complex.I*rho h r := by
    simpa only [rho,mul_assoc] using
      CarryRadialFlow.original_rotated_response (((r:ℂ)+1)*(h:ℂ))
  rw [hq i,hq j]
  have hn : (h:ℂ)≠0 := by exact_mod_cast hh
  field_simp [hn]
  ring_nf
  norm_num [Complex.I_sq]

theorem critical_physical_energy (a : ℝ) :
    ∀ᶠ k : ℕ in atTop,
      ‖(physicalCompletedFiniteSource k (CarryCubicOdd.criticalOddSource a k)).1‖^2-
        ‖(physicalCompletedFiniteSource k (CarryCubicOdd.criticalOddSource a k)).2‖^2=
          (criticalEnergy a (canonicalGreenJetStep k)).re := by
  filter_upwards [canonicalCompletedNativeRadialProjectiveChiral_eventually_regular 4] with k hk
  have he := physical_response_pair 4 k (criticalRaw a (canonicalGreenJetStep k))
    (criticalRaw a (canonicalGreenJetStep k)) (fun i => (hk i).2.1) (fun i => (hk i).2.2)
  rw [critical_curve_eq_original] at he
  have hs : radialFourSourceStep k≠0 := by unfold radialFourSourceStep; positivity
  have hc := critical_response_energy a (radialFourSourceStep k) hs
  rw [← canonicalGreenJetStep_eq_radialFourSourceStep k] at hc
  rw [hc] at he
  have hn := CarryTailReturn.signed_diagonal_norm
    (physicalCompletedFiniteSource k (CarryCubicOdd.criticalOddSource a k))
  have hr := congrArg Complex.re he
  norm_num [Complex.mul_re] at hr
  exact hn.symm.trans hr

/-- Physical orientation in the true second odd critical direction. This
does not use positivity of its limiting pivot. -/
theorem critical_original_eventually_above :
    ∀ᶠ k : ℕ in atTop, criticalLimit criticalParameter<
      ‖(physicalCompletedFiniteSource k (CarryCubicOdd.criticalOddSource criticalParameter k)).1‖^2-
        ‖(physicalCompletedFiniteSource k (CarryCubicOdd.criticalOddSource criticalParameter k)).2‖^2 := by
  filter_upwards [critical_physical_energy criticalParameter,critical_energy_eventually_above] with k he hp
  rw [he]
  exact hp

theorem critical_original_correction_tendsto :
    Tendsto (fun k : ℕ =>
      (‖(physicalCompletedFiniteSource k (CarryCubicOdd.criticalOddSource criticalParameter k)).1‖^2-
        ‖(physicalCompletedFiniteSource k (CarryCubicOdd.criticalOddSource criticalParameter k)).2‖^2-
          criticalLimit criticalParameter)/(radialFourSourceStep k)^2)
      atTop (nhds (criticalCorrection criticalParameter)) := by
  have hl := Complex.continuous_re.continuousAt.tendsto.comp
    (critical_correction_tendsto criticalParameter)
  apply hl.congr'
  filter_upwards [critical_physical_energy criticalParameter] with k hk
  dsimp only [Function.comp_def]
  rw [hk]
  simp only [canonicalGreenJetStep_eq_radialFourSourceStep,← Complex.ofReal_pow,
    Complex.div_ofReal_re,Complex.sub_re,Complex.ofReal_re]

end
end CarryMovingRadial
