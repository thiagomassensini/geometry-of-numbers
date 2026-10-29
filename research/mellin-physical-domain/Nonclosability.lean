import MellinLimits
import Mathlib.LinearAlgebra.LinearPMap

/-! No bounded or closed linear extension of this literal finite Mellin port
in the ORIGINAL physical L2 topology. This is not a no-go for the full Green
state with additional native regularity, and not a statement about Hankel sign. -/
namespace CarryMellinDomain
open CarrySourcePrime CarrySelfAdjointOperator Filter Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

/-- The actual finite readout relation, restricted even to ZERO boundary trace. -/
def finiteZeroTraceGraph (p : ℕ) : Set (CanonicalCompletedNativeChiralCauchyCarrier × ℝ) :=
  {z | ∃ (N : ℕ) (c : Fin (N+1) → ℝ), c 0=0 ∧
    z=(ContinuousMap.toLp 2 MeasureTheory.volume ℂ (originalContinuousSynthesis c),
      ∫ u in (0:ℝ)..(p:ℝ)⁻¹, mellinTailPolynomial c u)}

theorem concentration_mem_graph (p n : ℕ) :
    (physicalConcentration n,concentrationReadout p n)∈finiteZeroTraceGraph p :=
  ⟨n+1,concentratingCoefficients n,concentrating_trace_zero n,rfl⟩

theorem zero_mem_finite_graph (p : ℕ) :
    (0,0)∈finiteZeroTraceGraph p := by
  refine ⟨0,(fun _ => 0),rfl,?_⟩
  simp [originalContinuousSynthesis,mellinTailPolynomial]

/-- The closure contains a nonzero vertical vector: zero physical source,
nonzero scalar readout. This is the concrete graph obstruction. -/
theorem zero_one_mem_graph_closure (p : Nat.Primes) :
    (0,1)∈closure (finiteZeroTraceGraph p) := by
  have h := physical_concentration_tendsto_zero.prodMk_nhds (concentration_readout_tendsto_one p)
  apply isClosed_closure.mem_of_tendsto h
  exact Eventually.of_forall fun n => subset_closure (concentration_mem_graph p n)

theorem closure_not_single_valued (p : Nat.Primes) :
    ¬ (∀ x a b, (x,a)∈closure (finiteZeroTraceGraph p) →
      (x,b)∈closure (finiteZeroTraceGraph p) → a=b) := by
  intro h
  have he := h 0 0 1 (subset_closure (zero_mem_finite_graph p)) (zero_one_mem_graph_closure p)
  exact zero_ne_one he

/-- No bound of the readout by the unchanged physical norm exists. -/
theorem mellin_readout_no_norm_bound (p : Nat.Primes) :
    ¬ ∃ C : ℝ, ∀ n : ℕ, |concentrationReadout p n|≤C*‖physicalConcentration n‖ := by
  rintro ⟨C,hC⟩
  have hl : Tendsto (fun n => |concentrationReadout p n|) atTop (nhds 1) := by
    simpa using (concentration_readout_tendsto_one p).abs
  have hr : Tendsto (fun n => C*‖physicalConcentration n‖) atTop (nhds 0) := by
    simpa using physical_concentration_tendsto_zero.norm.const_mul C
  have hle := le_of_tendsto_of_tendsto hl hr (Eventually.of_forall hC)
  norm_num at hle

/-- A continuous real-linear readout of the entire physical carrier cannot
agree with the original finite port, already on its zero-trace inputs. -/
theorem no_continuous_mellin_extension (p : Nat.Primes)
    (L : CanonicalCompletedNativeChiralCauchyCarrier →L[ℝ] ℝ)
    (hL : ∀ z∈finiteZeroTraceGraph p, L z.1=z.2) : False := by
  have h0 : Tendsto (fun n => L (physicalConcentration n)) atTop (nhds 0) := by
    simpa only [Function.comp_def,map_zero] using
      L.continuous.continuousAt.tendsto.comp physical_concentration_tendsto_zero
  have h1 : Tendsto (fun n => L (physicalConcentration n)) atTop (nhds 1) :=
    (concentration_readout_tendsto_one p).congr'
      (Eventually.of_forall fun n => (hL _ (concentration_mem_graph p n)).symm)
  have he := tendsto_nhds_unique h0 h1
  exact zero_ne_one he

/-- Even an unbounded CLOSED partial operator cannot extend the finite port
in this topology. Hence restricting to zero trace alone does not cure it. -/
theorem no_closed_mellin_extension (p : Nat.Primes)
    (T : CanonicalCompletedNativeChiralCauchyCarrier →ₗ.[ℝ] ℝ)
    (hclosed : IsClosed (T.graph : Set (CanonicalCompletedNativeChiralCauchyCarrier × ℝ)))
    (hext : finiteZeroTraceGraph p ⊆ T.graph) : False := by
  have hm : (0,1)∈T.graph := (closure_minimal hext hclosed) (zero_one_mem_graph_closure p)
  obtain ⟨x,hx,hT⟩ := (LinearPMap.mem_graph_iff T).mp hm
  have hx0 : x=0 := Subtype.ext hx
  rw [hx0] at hT
  change T.toFun 0=1 at hT
  rw [map_zero] at hT
  exact zero_ne_one hT

/-- Keeping the ORIGINAL boundary coefficient as a separate input coordinate
still does not yield a bounded extension: every witness has exactly trace zero. -/
theorem no_continuous_mellin_extension_with_trace (p : Nat.Primes)
    (L : (CanonicalCompletedNativeChiralCauchyCarrier × ℝ) →L[ℝ] ℝ)
    (hL : ∀ n, L (physicalConcentration n,0)=concentrationReadout p n) : False := by
  have hv : Tendsto (fun n => (physicalConcentration n,(0:ℝ))) atTop (nhds (0,0)) :=
    physical_concentration_tendsto_zero.prodMk_nhds tendsto_const_nhds
  have h0 : Tendsto (fun n => L (physicalConcentration n,0)) atTop (nhds 0) := by
    simpa only [Function.comp_def,show L (0,0)=0 from L.map_zero] using
      L.continuous.continuousAt.tendsto.comp hv
  have h1 : Tendsto (fun n => L (physicalConcentration n,0)) atTop (nhds 1) :=
    (concentration_readout_tendsto_one p).congr' (Eventually.of_forall fun n => (hL n).symm)
  exact zero_ne_one (tendsto_nhds_unique h0 h1)

/-- The same graph obstruction with the boundary coordinate explicitly kept.
The witnesses live at trace zero, so adding this datum does not remove them. -/
theorem no_closed_mellin_extension_with_trace (p : Nat.Primes)
    (T : (CanonicalCompletedNativeChiralCauchyCarrier × ℝ) →ₗ.[ℝ] ℝ)
    (hclosed : IsClosed (T.graph : Set ((CanonicalCompletedNativeChiralCauchyCarrier × ℝ) × ℝ)))
    (hext : ∀ (N : ℕ) (c : Fin (N+1) → ℝ),
      ((ContinuousMap.toLp 2 MeasureTheory.volume ℂ (originalContinuousSynthesis c),c 0),
        ∫ u in (0:ℝ)..(p:ℝ)⁻¹, mellinTailPolynomial c u)∈T.graph) : False := by
  have hv : Tendsto (fun n => (physicalConcentration n,(0:ℝ))) atTop (nhds (0,0)) :=
    physical_concentration_tendsto_zero.prodMk_nhds tendsto_const_nhds
  have hm : ((0,0),1)∈T.graph := by
    apply hclosed.mem_of_tendsto (hv.prodMk_nhds (concentration_readout_tendsto_one p))
    exact Eventually.of_forall fun n => by
      have h := hext (n+1) (concentratingCoefficients n)
      rw [concentrating_trace_zero] at h
      change ((physicalConcentration n,0),concentrationReadout p n)∈T.graph at h
      exact h
  obtain ⟨x,hx,hT⟩ := (LinearPMap.mem_graph_iff T).mp hm
  have hx0 : x=0 := Subtype.ext hx
  rw [hx0] at hT
  change T.toFun 0=1 at hT
  rw [map_zero] at hT
  exact zero_ne_one hT

end
end CarryMellinDomain
