import RemainderJets
import QuarticEnvelope

/-! Exact infinite TFVD acceleration of the already synthesized ordinary
return, proved at each fixed normalized jet order. No derivative/limit
interchange or discarded endpoint is used. -/
namespace CarryFourthTail
open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.BaseTwoCompletion
open CarryCellTail CarryMaterialParts Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

theorem native_jet_window (m M N : ℕ) :
    (∑ k ∈ Finset.range N, cellJet m (k+M)) =
      boundaryJet m (4*M+3)-boundaryJet m (4*M+3+4*N)+
        ∑ k ∈ Finset.range N, remainderJet m (4*M+3+4*k) := by
  have he : (fun t => ∑ k ∈ Finset.range N, baseTwoCriticalCenterCell t (k+M)) =
      fun t => nativeBoundary (4*M+3) t-nativeBoundary (4*M+3+4*N) t+
        ∑ k ∈ Finset.range N, nativeRemainder (4*M+3+4*k) t :=
    funext (fun t => native_tail_window_acceleration t M N)
  have h := congrArg (rJet m) he
  rw [rJet_sum _ _ (fun k _ => cell_real_analytic (k+M)),
    rJet_add (f:=fun t => nativeBoundary (4*M+3) t-nativeBoundary (4*M+3+4*N) t)
      (g:=fun t => ∑ k ∈ Finset.range N, nativeRemainder (4*M+3+4*k) t)
      ((native_boundary_analytic _ (by omega)).sub (native_boundary_analytic _ (by omega)))
      ((Finset.range N).analyticAt_fun_sum (fun k _ => native_remainder_analytic _ (by omega))),
    rJet_sub (native_boundary_analytic _ (by omega)) (native_boundary_analytic _ (by omega)),
    rJet_sum _ _ (fun k _ => native_remainder_analytic _ (by omega))] at h
  simpa only [rJet, ← cell_jet_source, boundaryJet, remainderJet] using h

theorem boundary_jet_vanishes (m M : ℕ) :
    Tendsto (fun N => boundaryJet m (4*M+3+4*N)) atTop (nhds 0) := by
  have hn : Tendsto (fun N : ℕ => 4*M+3+4*N) atTop atTop :=
    tendsto_atTop_mono (fun N => by dsimp; omega) tendsto_id
  have hc : Tendsto (fun N : ℕ => ((4*M+3+4*N:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  have hi : Tendsto (fun N : ℕ => (2:ℝ)^m/((4*M+3+4*N:ℕ):ℝ)) atTop (nhds 0) := by
    simpa only [Function.comp_def, mul_zero, div_eq_mul_inv] using
      (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hc))
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _) (fun N => boundary_jet_bound m _ (by omega)) hi

theorem remainder_jets_summable (m M : ℕ) :
    Summable (fun k : ℕ => ‖remainderJet m (4*(k+M)+3)‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun k => by simpa only [mul_one_div] using remainder_jet_bound m (4*(k+M)+3) (by omega))
    ((quartic_cell_summable M).mul_left (30*2^m))

theorem remainder_series_bound (m M : ℕ) (hM : 0 < M) :
    ‖∑' k, remainderJet m (4*(k+M)+3)‖ ≤ 30*2^m/(12*(4*(M:ℝ)-1)^3) := by
  apply (norm_tsum_le_tsum_norm (remainder_jets_summable m M)).trans
  calc
    ∑' k, ‖remainderJet m (4*(k+M)+3)‖ ≤
        ∑' k, (30*2^m)*((1:ℝ)/((4*(k+M)+3:ℕ):ℝ)^4) :=
      (remainder_jets_summable m M).tsum_le_tsum
        (fun k => by simpa only [mul_one_div] using remainder_jet_bound m _ (by omega))
        ((quartic_cell_summable M).mul_left _)
    _ = (30*2^m)*(∑' k : ℕ, (1:ℝ)/((4*(k+M)+3:ℕ):ℝ)^4) := tsum_mul_left
    _ ≤ 30*2^m/(12*(4*(M:ℝ)-1)^3) := by
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left (quartic_cell_tail M hM)
        (by positivity : (0:ℝ) ≤ 30*2^m)

/-- Both endpoints survived the finite identity; only now the second is
proved to vanish. The remaining tail is the same original ordinary return. -/
theorem infinite_jet_acceleration (m M : ℕ) :
    (∑' k, cellJet m (k+M)) = boundaryJet m (4*M+3)+
      ∑' k, remainderJet m (4*(k+M)+3) := by
  have hcell : Summable (fun k : ℕ => ‖cellJet m (k+M)‖) :=
    (cell_jet_norm_summable m).comp_injective (by intro i j h; exact Nat.add_right_cancel h)
  have hl := hcell.of_norm.hasSum.tendsto_sum_nat
  have hr : Tendsto (fun N => boundaryJet m (4*M+3)-boundaryJet m (4*M+3+4*N)+
      ∑ k ∈ Finset.range N, remainderJet m (4*(k+M)+3)) atTop
      (nhds (boundaryJet m (4*M+3)+∑' k, remainderJet m (4*(k+M)+3))) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds.sub (boundary_jet_vanishes m M)).add
        (remainder_jets_summable m M).of_norm.hasSum.tendsto_sum_nat
  apply tendsto_nhds_unique hl
  apply hr.congr'
  exact .of_forall (fun N => by
    dsimp only
    rw [native_jet_window]
    simp only [show ∀ k : ℕ, 4*(k+M)+3=4*M+3+4*k by omega])

def acceleratedOrdinaryHead (M : ℕ) (t : ℝ) : ℂ :=
  ordinaryHead M t+nativeBoundary (4*M+3) t

def acceleratedOrdinaryTail (M : ℕ) (t : ℝ) : ℂ :=
  baseTwoCompletedBoundaryValue t-acceleratedOrdinaryHead M t

theorem accelerated_ordinary_head_analytic (M : ℕ) :
    AnalyticAt ℝ (acceleratedOrdinaryHead M) 0 :=
  (ordinary_head_analytic M).add (native_boundary_analytic _ (by omega))

theorem accelerated_ordinary_tail_analytic (M : ℕ) :
    AnalyticAt ℝ (acceleratedOrdinaryTail M) 0 :=
  beta_real_analytic.sub (accelerated_ordinary_head_analytic M)

theorem accelerated_ordinary_jet_exact (m M : ℕ) :
    rJet m (acceleratedOrdinaryTail M) = ∑' k, remainderJet m (4*(k+M)+3) := by
  unfold acceleratedOrdinaryTail
  rw [rJet_sub beta_real_analytic (accelerated_ordinary_head_analytic M)]
  unfold acceleratedOrdinaryHead
  rw [rJet_add (ordinary_head_analytic M) (native_boundary_analytic _ (by omega))]
  unfold ordinaryHead
  rw [rJet_sum _ _ (fun k _ => cell_real_analytic k)]
  simp only [rJet, ← cell_jet_source]
  rw [return_jet_head_tail m M, infinite_jet_acceleration m M]
  change _-(_+boundaryJet m (4*M+3)) = _
  ring

def acceleratedOrdinaryBudget (m M : ℕ) : ℝ := 30*2^m/(12*(4*(M:ℝ)-1)^3)

theorem accelerated_ordinary_jet_bound (m M : ℕ) (hM : 0 < M) :
    ‖rJet m (acceleratedOrdinaryTail M)‖ ≤ acceleratedOrdinaryBudget m M := by
  rw [accelerated_ordinary_jet_exact]
  exact remainder_series_bound m M hM
end
end CarryFourthTail
