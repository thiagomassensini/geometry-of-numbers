import InfiniteTiltLedger

namespace CarryTiltSlice
open CPFormal.Analytic.Cp CarrySelfAdjointOperator Filter
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem material_chart_hasDerivAt (t : ℝ) :
    HasDerivAt (fun d : ℝ => bracketedDirichletChart 3 (displacedParameter d t))
      (deriv (bracketedDirichletChart 3) (criticalParameter t)) 0 := by
  have hmem : criticalParameter t ∈ bracketHalfPlane := by
    change -1 < (criticalParameter t).re
    rw [criticalParameter_re]
    norm_num
  have hf := (analyticOnNhd_bracketedDirichletChart 3 (by norm_num) _ hmem).differentiableAt.hasDerivAt
  have hg : HasDerivAt (fun z : ℂ => z + criticalParameter t) 1 0 := by
    simpa using (hasDerivAt_id (0:ℂ)).add_const (criticalParameter t)
  have hf' : HasDerivAt (bracketedDirichletChart 3)
      (deriv (bracketedDirichletChart 3) (criticalParameter t)) (0 + criticalParameter t) := by simpa using hf
  have hh := (hf'.comp (0:ℂ) hg).comp_ofReal
  have he : (fun d : ℝ => ((d:ℂ) + criticalParameter t)) =
      (fun d : ℝ => displacedParameter d t) := by
    funext d
    unfold criticalParameter displacedParameter
    push_cast
    ring
  have hfin : HasDerivAt (fun d : ℝ => bracketedDirichletChart 3 ((d:ℂ)+criticalParameter t))
      (deriv (bracketedDirichletChart 3) (criticalParameter t)) 0 := by
    simpa only [Function.comp_def,zero_add,mul_one,Complex.ofReal_zero] using hh
  have hfun := congrArg (fun f : ℝ → ℂ => fun d => bracketedDirichletChart 3 (f d)) he
  rw [hfun] at hfin
  exact hfin

theorem infiniteCarrierRemainder_hasDerivAt (t : ℝ) :
    HasDerivAt (infiniteCarrierRemainder t)
      (deriv (bracketedDirichletChart 3) (criticalParameter t) - infiniteMixedTiltResponse (t:ℂ)) 0 := by
  have he : (infiniteCarrierRemainder t) =ᶠ[𝓝 (0:ℝ)]
      (fun d : ℝ => bracketedDirichletChart 3 (displacedParameter d t) - 1 - infiniteTransverseTilt t d) := by
    have hI : Set.Ioo (-(1/4:ℝ)) (1/4:ℝ) ∈ 𝓝 (0:ℝ) := isOpen_Ioo.mem_nhds (by norm_num)
    filter_upwards [hI] with d hd
    have h := infinite_c3_tilt_carrier_ledger t d hd.1 hd.2
    linear_combination -h
  have h := (material_chart_hasDerivAt t).sub_const 1 |>.sub (hasDerivAt_infiniteTransverseTilt t)
  exact h.congr_of_eventuallyEq he

theorem infinite_material_transverse_ledger (t : ℝ) :
    deriv (fun d : ℝ => bracketedDirichletChart 3 (displacedParameter d t)) 0 =
      infiniteMixedTiltResponse (t:ℂ) + deriv (infiniteCarrierRemainder t) 0 := by
  rw [(material_chart_hasDerivAt t).deriv, (infiniteCarrierRemainder_hasDerivAt t).deriv]
  ring

#print axioms material_chart_hasDerivAt
#print axioms infiniteCarrierRemainder_hasDerivAt
#print axioms infinite_material_transverse_ledger
end
end CarryTiltSlice
