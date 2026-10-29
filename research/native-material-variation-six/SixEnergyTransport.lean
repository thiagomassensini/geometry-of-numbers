import SixSign

namespace CarryMaterialVariation
open CarrySelfAdjointOperator CarryMovingRadial NativeLaguerre CarrySelfAdjointOperator.PhysicalSewing
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem six_weight_real (u v h : ℝ) (i : Fin 6) :
    conj (sixWeight u v (h:ℂ) i)=sixWeight u v (h:ℂ) i := by
  fin_cases i <;> norm_num [sixWeight,map_sub,map_mul,map_pow,map_ofNat]

theorem six_raw_product (u v h : ℝ) (i j : Fin 6) :
    conj (sixRaw u v (h:ℂ) i)*sixRaw u v (h:ℂ) j=
      sixWeight u v (h:ℂ) i*sixWeight u v (h:ℂ) j/(14400*(h:ℂ)^10) := by
  unfold sixRaw
  simp only [map_mul,map_neg,map_div₀,map_pow,map_ofNat,Complex.conj_I,Complex.conj_ofReal,
    six_weight_real]
  ring_nf
  norm_num [Complex.I_sq]

/-- Scalar response is identified ONLY after the full state and all crosses.
This is the SAME raw critical source, with its scale and phase preserved. -/
theorem six_response_energy (u v h : ℝ) (hh : h≠0) :
    responsePair 6 h (sixRaw u v (h:ℂ)) (sixRaw u v (h:ℂ))=sixEnergy u v (h:ℂ) := by
  unfold responsePair sixEnergy sixKernel
  simp_rw [six_raw_product]
  rw [Finset.sum_div]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_div,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hq (r : Fin 6) : completedNativeOperatorLogDerivative (Complex.I*((r:ℂ)+1)*(h:ℂ))=
      2*Complex.I*CarryMovingRadial.rho h r := by
    simpa only [CarryMovingRadial.rho,mul_assoc] using
      CarryRadialFlow.original_rotated_response (((r:ℂ)+1)*(h:ℂ))
  rw [hq i,hq j]
  have hn : (h:ℂ)≠0 := by exact_mod_cast hh
  field_simp [hn]
  ring_nf
  norm_num [Complex.I_sq]

theorem six_physical_energy (u v : ℝ) :
    ∀ᶠ k : ℕ in atTop,
      ‖(physicalCompletedFiniteSource k (sixInput u v k)).1‖^2-
        ‖(physicalCompletedFiniteSource k (sixInput u v k)).2‖^2=
          (sixEnergy u v (canonicalGreenJetStep k)).re := by
  filter_upwards [canonicalCompletedNativeRadialProjectiveChiral_eventually_regular 6] with k hk
  have he := physical_response_pair 6 k (sixRaw u v (canonicalGreenJetStep k))
    (sixRaw u v (canonicalGreenJetStep k)) (fun i => (hk i).2.1) (fun i => (hk i).2.2)
  rw [six_curve_eq_original] at he
  have hs : radialFourSourceStep k≠0 := by unfold radialFourSourceStep; positivity
  have hc := six_response_energy u v (radialFourSourceStep k) hs
  rw [← canonicalGreenJetStep_eq_radialFourSourceStep k] at hc
  rw [hc] at he
  have hn := CarryTailReturn.signed_diagonal_norm
    (physicalCompletedFiniteSource k (sixInput u v k))
  have hr := congrArg Complex.re he
  norm_num [Complex.mul_re] at hr
  exact hn.symm.trans hr

/-- Physical orientation in the true third odd critical direction. This
does not use positivity of its limiting pivot. -/
theorem six_original_eventually_above :
    ∀ᶠ k : ℕ in atTop, sixLimit sixU sixV<
      ‖(physicalCompletedFiniteSource k (sixInput sixU sixV k)).1‖^2-
        ‖(physicalCompletedFiniteSource k (sixInput sixU sixV k)).2‖^2 := by
  filter_upwards [six_physical_energy sixU sixV,six_energy_eventually_above] with k he hp
  rw [he]
  exact hp

theorem six_original_correction_tendsto :
    Tendsto (fun k : ℕ =>
      (‖(physicalCompletedFiniteSource k (sixInput sixU sixV k)).1‖^2-
        ‖(physicalCompletedFiniteSource k (sixInput sixU sixV k)).2‖^2-
          sixLimit sixU sixV)/(radialFourSourceStep k)^2)
      atTop (nhds (sixCorrection sixU sixV)) := by
  have hl := Complex.continuous_re.continuousAt.tendsto.comp
    (six_correction_tendsto sixU sixV)
  apply hl.congr'
  filter_upwards [six_physical_energy sixU sixV] with k hk
  dsimp only [Function.comp_def]
  rw [hk]
  simp only [canonicalGreenJetStep_eq_radialFourSourceStep,← Complex.ofReal_pow,
    Complex.div_ofReal_re,Complex.sub_re,Complex.ofReal_re]

end
end CarryMaterialVariation
