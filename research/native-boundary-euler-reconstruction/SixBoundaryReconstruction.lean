import AnalyticRadialTail
import SixEnergyTransport

namespace CarryBoundaryReconstruction
open CarrySelfAdjointOperator CarryMovingRadial CarryMaterialVariation NativeLaguerre Filter Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- Literal original six-address balance; both full physical legs remain. -/
def sixPhysical (k : ℕ) : ℝ :=
  ‖(physicalCompletedFiniteSource k (sixInput sixU sixV k)).1‖^2-
    ‖(physicalCompletedFiniteSource k (sixInput sixU sixV k)).2‖^2

theorem radial_step_positive (k : ℕ) : 0<radialFourSourceStep k := by
  unfold radialFourSourceStep
  positivity

theorem radial_step_decreasing (k : ℕ) : radialFourSourceStep (k+1)<radialFourSourceStep k := by
  unfold radialFourSourceStep
  apply (inv_lt_inv₀ (by positivity) (by positivity)).mpr
  push_cast
  linarith

theorem radial_step_tendsto : Tendsto radialFourSourceStep atTop (nhds 0) := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp canonicalGreenJetStep_tendsto_zero
  simpa only [Function.comp_def,canonicalGreenJetStep_eq_radialFourSourceStep,
    Complex.ofReal_re,Complex.zero_re] using h

/-- Full remainder from the original response, not a fit to the pivot. -/
theorem six_physical_analytic_extension : ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧
    ∀ᶠ k : ℕ in atTop, sixPhysical k=
      quadraticExtension (sixLimit sixU sixV) (sixCorrection sixU sixV) R (radialFourSourceStep k) := by
  obtain ⟨R,hRa,hR⟩ := six_exact_remainder sixU sixV
  refine ⟨R,hRa,?_⟩
  filter_upwards [six_physical_energy sixU sixV,canonicalGreenJetStep_tendsto_zero.eventually hR]
    with k hp hk
  have hn : canonicalGreenJetStep k≠0 := by
    rw [canonicalGreenJetStep_eq_radialFourSourceStep]
    exact_mod_cast (radial_step_positive k).ne'
  have he : sixEnergy sixU sixV (canonicalGreenJetStep k)=
      (sixLimit sixU sixV:ℂ)+(sixCorrection sixU sixV:ℂ)*canonicalGreenJetStep k^2+
        canonicalGreenJetStep k^3*R (canonicalGreenJetStep k) := by
    unfold sixEnergy
    rw [hk]
    field_simp [hn]
  change sixPhysical k=_ at hp
  rw [hp,he]
  simp only [quadraticExtension,canonicalGreenJetStep_eq_radialFourSourceStep,
    ← Complex.ofReal_pow,Complex.add_re,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero]

theorem six_physical_tendsto : Tendsto sixPhysical atTop (nhds (sixLimit sixU sixV)) := by
  obtain ⟨R,hR,he⟩ := six_physical_analytic_extension
  have heq : sixPhysical =ᶠ[atTop] (fun k => quadraticExtension
      (sixLimit sixU sixV) (sixCorrection sixU sixV) R (radialFourSourceStep k)) := he
  exact ((quadratic_extension_tendsto _ _ R hR).comp radial_step_tendsto).congr' heq.symm

/-- NEW: strict decrease of the complete balances at every sufficiently
late native radial step. No sign of the limiting residual is assumed. -/
theorem six_physical_eventually_decreasing :
    ∀ᶠ k : ℕ in atTop, sixPhysical (k+1)<sixPhysical k := by
  obtain ⟨R,hR,he⟩ := six_physical_analytic_extension
  obtain ⟨ε,hε,hm⟩ := quadratic_extension_strictMono _ _ R hR six_critical_correction_positive
  have hs : ∀ᶠ k : ℕ in atTop, radialFourSourceStep k<ε :=
    radial_step_tendsto.eventually_lt tendsto_const_nhds hε
  filter_upwards [he,(tendsto_add_atTop_nat 1).eventually he,hs] with k hk hk1 hs
  rw [hk,hk1]
  exact hm ⟨radial_step_positive _,(radial_step_decreasing k).trans hs⟩
    ⟨radial_step_positive _,hs⟩ (radial_step_decreasing k)

/-- Original finite-scale datum minus an absolutely summable positive tail.
The tail is not discarded, and its sign gives an UPPER bound on the boundary. -/
theorem six_boundary_tail : ∃ N : ℕ, ∀ K : ℕ, N≤K →
    (∀ j, 0<sixPhysical (K+j)-sixPhysical (K+j+1)) ∧
    HasSum (fun j => sixPhysical (K+j)-sixPhysical (K+j+1))
      (sixPhysical K-sixLimit sixU sixV) ∧
    Summable (fun j => |sixPhysical (K+j)-sixPhysical (K+j+1)|) ∧
    sixLimit sixU sixV=sixPhysical K-
      ∑' j, (sixPhysical (K+j)-sixPhysical (K+j+1)) := by
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp six_physical_eventually_decreasing
  refine ⟨N,fun K hK => ?_⟩
  have hd (j : ℕ) : 0<sixPhysical (K+j)-sixPhysical (K+j+1) :=
    sub_pos.mpr (hN _ (by omega))
  have hs := radial_drop_hasSum sixPhysical _ six_physical_tendsto K (fun j => (hd j).le)
  refine ⟨hd,hs,?_,?_⟩
  · simpa only [abs_of_pos (hd _)] using hs.summable
  · rw [hs.tsum_eq]
    ring

/-- Quantitative scale of the ENTIRE original accumulated tail. The factors
1/2 and 3/2 are margins from the proved limit, not changes to the source. -/
theorem six_accumulated_tail_scale : ∃ N : ℕ, ∀ K : ℕ, N≤K →
    HasSum (fun j => sixPhysical (K+j)-sixPhysical (K+j+1))
      (sixPhysical K-sixLimit sixU sixV) ∧
    (sixCorrection sixU sixV/2)*(radialFourSourceStep K)^2 <
      ∑' j, (sixPhysical (K+j)-sixPhysical (K+j+1)) ∧
    (∑' j, (sixPhysical (K+j)-sixPhysical (K+j+1))) <
      (3*sixCorrection sixU sixV/2)*(radialFourSourceStep K)^2 := by
  have hl : Tendsto (fun k => (sixPhysical k-sixLimit sixU sixV)/(radialFourSourceStep k)^2)
      atTop (nhds (sixCorrection sixU sixV)) := six_original_correction_tendsto
  have hC := six_critical_correction_positive
  have hlo : ∀ᶠ k : ℕ in atTop, sixCorrection sixU sixV/2 <
      (sixPhysical k-sixLimit sixU sixV)/(radialFourSourceStep k)^2 :=
    Filter.Tendsto.eventually_lt tendsto_const_nhds hl (by linarith)
  have hhi : ∀ᶠ k : ℕ in atTop,
      (sixPhysical k-sixLimit sixU sixV)/(radialFourSourceStep k)^2 <3*sixCorrection sixU sixV/2 :=
    Filter.Tendsto.eventually_lt hl tendsto_const_nhds (by linarith)
  obtain ⟨N,hN⟩ := six_boundary_tail
  obtain ⟨M,hM⟩ := Filter.eventually_atTop.mp (hlo.and hhi)
  refine ⟨max N M,fun K hK => ?_⟩
  have hs := (hN K (le_trans (le_max_left _ _) hK)).2.1
  obtain ⟨ha,hb⟩ := hM K (le_trans (le_max_right _ _) hK)
  have hp := sq_pos_of_pos (radial_step_positive K)
  refine ⟨hs,?_,?_⟩
  · rw [hs.tsum_eq]
    exact (lt_div_iff₀ hp).mp ha
  · rw [hs.tsum_eq]
    exact (div_lt_iff₀ hp).mp hb

end
end CarryBoundaryReconstruction
