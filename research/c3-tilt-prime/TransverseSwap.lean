import TransverseBound
import Mathlib.Analysis.Calculus.Deriv.Slope

namespace CarryTiltSlice
open CPFormal.Analytic.Cp CarrySelfAdjointOperator Filter
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000

def infiniteTransverseTilt (t d : ℝ) : ℂ :=
  ∑' k : ℕ, canonicalCriticalWeightedTiltBlock k (displacedParameter d t)

theorem infiniteTransverseTilt_zero (t : ℝ) : infiniteTransverseTilt t 0 = 0 := by
  unfold infiniteTransverseTilt
  have h : (fun k : ℕ => canonicalCriticalWeightedTiltBlock k (displacedParameter 0 t)) = 0 := by
    funext k
    rw [tilted_cell_displaced,cpTilt_zero 3 (by norm_num)]
    simp
  rw [h]
  change (∑' _ : ℕ, (0:ℂ)) = 0
  exact tsum_zero

theorem slope_tendsto_cell (k : ℕ) (t : ℝ) :
    Tendsto (fun d : ℝ => transverseSlope k t d) (𝓝[≠] (0:ℝ))
      (𝓝 (mixedTiltWave k (t:ℂ))) := by
  have he : localCriticalLineCarrier (criticalParameter t) (canonicalRealCpCenter k) 0 *
      (carryTiltThreeFirstSensitivity (canonicalRealCpCenter k):ℂ) = mixedTiltWave k (t:ℂ) :=
    (tilt_cell_transverse_derivative k t).deriv.symm.trans (mixed_tilt_wave_of_real k t)
  rw [← he]
  simpa [transverseSlope] using (tilt_cell_transverse_derivative k t).tendsto_slope_zero

theorem transverse_bound_summable : Summable (fun k : ℕ => 2 * (((k+1:ℕ):ℝ)^(-(3/2):ℝ))) := by
  have hb : Summable (fun k : ℕ => (k:ℝ)^(-(3/2):ℝ)) := Real.summable_nat_rpow.mpr (by norm_num)
  have hs := hb.comp_injective (show Function.Injective (fun k : ℕ => k+1) by
    intro a b h; exact Nat.add_right_cancel h)
  simpa [Function.comp_def] using hs.mul_left 2

theorem transverseSlope_tsum_tendsto (t : ℝ) :
    Tendsto (fun d : ℝ => ∑' k : ℕ, transverseSlope k t d) (𝓝[≠] (0:ℝ))
      (𝓝 (infiniteMixedTiltResponse (t:ℂ))) := by
  unfold infiniteMixedTiltResponse
  apply tendsto_tsum_of_dominated_convergence transverse_bound_summable (fun k => slope_tendsto_cell k t)
  have hI : Set.Ioo (-(1/4:ℝ)) (1/4:ℝ) ∈ 𝓝[≠] (0:ℝ) :=
    nhdsWithin_le_nhds (isOpen_Ioo.mem_nhds (by norm_num))
  have hne : ({0}ᶜ : Set ℝ) ∈ 𝓝[≠] (0:ℝ) := self_mem_nhdsWithin
  filter_upwards [hI,hne] with d hd hdne
  intro k
  exact transverseSlope_norm_le k t d hd.1 hd.2 (by simpa using hdne)

theorem transverseSlope_tsum_eq (t d : ℝ) :
    (∑' k : ℕ, transverseSlope k t d) =
      d⁻¹ • (infiniteTransverseTilt t d - infiniteTransverseTilt t 0) := by
  rw [infiniteTransverseTilt_zero,sub_zero]
  unfold transverseSlope infiniteTransverseTilt
  simp only [tilted_cell_displaced,cpTilt_zero 3 (by norm_num),Complex.ofReal_zero,mul_zero,sub_zero]
  simp only [Complex.real_smul]
  rw [tsum_mul_left]

theorem hasDerivAt_infiniteTransverseTilt (t : ℝ) :
    HasDerivAt (infiniteTransverseTilt t) (infiniteMixedTiltResponse (t:ℂ)) 0 := by
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  have h := transverseSlope_tsum_tendsto t
  simp_rw [transverseSlope_tsum_eq] at h
  simpa only [zero_add] using h

#print axioms transverseSlope_tsum_tendsto
#print axioms hasDerivAt_infiniteTransverseTilt
theorem infiniteTransverseTilt_summable (t d : ℝ) (hdlo : -(1/4:ℝ) < d)
    (hdhi : d < 1/4) :
    Summable (fun k : ℕ => canonicalCriticalWeightedTiltBlock k (displacedParameter d t)) := by
  by_cases hd : d = 0
  · subst d
    have hzero : (fun k : ℕ => canonicalCriticalWeightedTiltBlock k (displacedParameter 0 t)) = 0 := by
      funext k
      rw [tilted_cell_displaced,cpTilt_zero 3 (by norm_num)]
      simp
    rw [hzero]
    exact summable_zero
  · have hs : Summable (fun k : ℕ => transverseSlope k t d) :=
      transverse_bound_summable.of_norm_bounded (fun k => transverseSlope_norm_le k t d hdlo hdhi hd)
    have he : (fun k : ℕ => (d:ℂ)*transverseSlope k t d) =
        (fun k : ℕ => canonicalCriticalWeightedTiltBlock k (displacedParameter d t)) := by
      funext k
      have hzero : canonicalCriticalWeightedTiltBlock k (displacedParameter 0 t) = 0 := by
        rw [tilted_cell_displaced,cpTilt_zero 3 (by norm_num)]
        simp
      unfold transverseSlope
      rw [hzero,sub_zero]
      simp only [Complex.real_smul,Complex.ofReal_inv]
      have hdc : (d:ℂ) ≠ 0 := by exact_mod_cast hd
      field_simp
    rw [← he]
    exact hs.mul_left (d:ℂ)

#print axioms infiniteTransverseTilt_summable

end
end CarryTiltSlice
