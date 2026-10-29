import NativeSynthesis

namespace CarryVerticalSynthesis
open CarrySelfAdjointOperator CPFormal.Analytic.Cp
open scoped BigOperators InnerProductSpace
open Filter Topology
noncomputable section
set_option autoImplicit false

theorem native_synthesis_difference_bound (X Y : NativeGpreTowerHilbert) :
    ‖nativeSynthesis X - nativeSynthesis Y‖ ≤ 2 * ‖X - Y‖ := by
  rw [← map_sub]
  exact native_synthesis_bound (X - Y)

/-- Both independent tails, including their tail-tail crossing, remain exact. -/
theorem native_synthesis_pairing_head_tail (Xh Xt Yh Yt : NativeGpreTowerHilbert) :
    inner ℂ (nativeSynthesis (Xh + Xt)) (nativeSynthesis (Yh + Yt)) =
      inner ℂ (nativeSynthesis Xh) (nativeSynthesis Yh) +
      inner ℂ (nativeSynthesis Xh) (nativeSynthesis Yt) +
      inner ℂ (nativeSynthesis Xt) (nativeSynthesis Yh) +
      inner ℂ (nativeSynthesis Xt) (nativeSynthesis Yt) := by
  simp only [map_add, inner_add_left, inner_add_right]
  ring

theorem native_synthesis_prefix_tendsto (X : NativeGpreTowerHilbert) :
    Tendsto (fun N => ∑ j ∈ Finset.range N, (X j) • completedNativeChiralCauchyFeature j)
      atTop (𝓝 (nativeSynthesis X)) :=
  (native_synthesis_hasSum X).tendsto_sum_nat

/-- A coherent all-order family for the ORIGINAL Cauchy kernel; no canonical
moment is used to manufacture this source or to choose a prefix. -/
theorem native_synthesis_prefix_pairing_tendsto (X Y : NativeGpreTowerHilbert) :
    Tendsto (fun N => inner ℂ
      (∑ i ∈ Finset.range N, (X i) • completedNativeChiralCauchyFeature i)
      (∑ j ∈ Finset.range N, (Y j) • completedNativeChiralCauchyFeature j))
      atTop (𝓝 (inner ℂ (nativeSynthesis X) (nativeSynthesis Y))) :=
  (native_synthesis_prefix_tendsto X).inner (native_synthesis_prefix_tendsto Y)

end
end CarryVerticalSynthesis
