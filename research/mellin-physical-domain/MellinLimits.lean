import FamilyEnergy
import Mathlib.Analysis.SpecificLimits.Basic

namespace CarryMellinDomain
open CarrySourcePrime CarrySelfAdjointOperator CPFormal.Analytic.Cp Filter Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

def concentrationReadout (p n : ℕ) : ℝ :=
  ∫ u in (0:ℝ)..(p:ℝ)⁻¹, mellinTailPolynomial (concentratingCoefficients n) u

/-- The readout is still the original source-dependent prime observation. -/
theorem concentration_readout_native (p : Nat.Primes) (n : ℕ) :
    concentrationReadout p n=primeReadout p
      (RealFirstNative.primeContractionLinear (finiteTowerSynthesis (concentratingCoefficients n))) :=
  mellin_integral_prime_readout (concentratingCoefficients n) p

theorem concentration_readout_formula (p n : ℕ) :
    concentrationReadout p n=1-(1-(p:ℝ)⁻¹)^(n+1) := by
  unfold concentrationReadout
  simp_rw [concentrating_tail_polynomial]
  rw [intervalIntegral.integral_const_mul,one_sub_integral]
  have hn : (n:ℝ)+1≠0 := by positivity
  field_simp

theorem physical_concentration_tendsto_zero :
    Tendsto physicalConcentration atTop (nhds 0) := by
  have hb : Tendsto (fun n : ℕ => 6/((n:ℝ)+1)^2) atTop (nhds 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).pow 2 |>.const_mul 6
    have he : (fun n : ℕ => 6/((n:ℝ)+1)^2)=(fun n : ℕ => 6*(1/((n:ℝ)+1))^2) := by
      funext n
      field_simp [show (n:ℝ)+1≠0 by positivity]
    rw [he]
    simpa using h
  have hs : Tendsto (fun n : ℕ => ‖physicalConcentration n‖^2) atTop (nhds 0) :=
    squeeze_zero (fun n => sq_nonneg _) physical_concentration_norm_sq_le hb
  have hnorm : Tendsto (fun n : ℕ => ‖physicalConcentration n‖) atTop (nhds 0) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp hs
    simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using h
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm

/-- One fixed prime camera already detects a nonzero limit at physical zero. -/
theorem concentration_readout_tendsto_one (p : Nat.Primes) :
    Tendsto (concentrationReadout p) atTop (nhds 1) := by
  have hp0 : 0<(p:ℝ) := by exact_mod_cast p.prop.pos
  have hp1 : (1:ℝ)≤(p:ℝ) := by exact_mod_cast p.prop.one_lt.le
  have hi : (p:ℝ)⁻¹≤1 := by
    simpa only [one_div,inv_one] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hp1
  have ha0 : 0≤1-(p:ℝ)⁻¹ := by linarith
  have ha1 : 1-(p:ℝ)⁻¹<1 := by have := inv_pos.mpr hp0; linarith
  have hpow := (tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1).comp (tendsto_add_atTop_nat 1)
  have h := (tendsto_const_nhds (x:=(1:ℝ))).sub hpow
  have h' : Tendsto (fun n : ℕ => 1-(1-(p:ℝ)⁻¹)^(n+1)) atTop (nhds 1) := by
    simpa only [Function.comp_def,sub_zero] using h
  exact h'.congr' (Eventually.of_forall fun n => (concentration_readout_formula p n).symm)

end
end CarryMellinDomain
