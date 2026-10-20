import CriticalRelative

namespace CarryCriticalRelative
open CarrySelfAdjointOperator CarrySelfAdjointOperator.ChiralReturn CarryCriticalSource
open Filter Topology
open scoped BigOperators InnerProductSpace
noncomputable section

/-- Polarized leading cancellation, retaining both channels and arbitrary
pairs of critical orders and sectors. No diagonal-only inference. -/
theorem critical_scaled_cross_tendsto_zero (s t : Fin 2) (n r : ℕ) :
    Tendsto (fun k =>
      inner ℂ
        (observationScale k (criticalOrder s n) •
          (criticalIncident s n k : CanonicalCompletedNativeChiralCauchyCarrier))
        (observationScale k (criticalOrder t r) •
          (criticalIncident t r k : CanonicalCompletedNativeChiralCauchyCarrier)) -
      inner ℂ
        (observationScale k (criticalOrder s n) • criticalReturned s n k)
        (observationScale k (criticalOrder t r) • criticalReturned t r k))
      atTop (nhds 0) := by
  have hs := critical_whole_source_tendsto s n
  have ht := critical_whole_source_tendsto t r
  have h := (hs.fst_nhds.inner (𝕜 := ℂ) ht.fst_nhds).sub
    (hs.snd_nhds.inner (𝕜 := ℂ) ht.snd_nhds)
  change Tendsto (fun k =>
      inner ℂ
        (observationScale k (criticalOrder s n) •
          (criticalIncident s n k : CanonicalCompletedNativeChiralCauchyCarrier))
        (observationScale k (criticalOrder t r) •
          (criticalIncident t r k : CanonicalCompletedNativeChiralCauchyCarrier)) -
      inner ℂ
        (observationScale k (criticalOrder s n) • criticalReturned s n k)
        (observationScale k (criticalOrder t r) • criticalReturned t r k))
      atTop (nhds (inner ℂ (criticalLeadingState s n) (criticalLeadingState t r) -
        inner ℂ (-criticalLeadingState s n) (-criticalLeadingState t r))) at h
  simpa only [inner_neg_neg, sub_self] using h

end
end CarryCriticalRelative
