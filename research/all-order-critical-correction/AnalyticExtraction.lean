import SourceTaylor

/-! A generic coefficient extraction lemma. All cancellation assumptions are
about Taylor coefficients; this lemma supplies no positivity hypothesis. -/
namespace CarryAllOrderCorrection
open CarrySelfAdjointOperator Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

def taylorCoefficient (f : ℂ → ℂ) (d : ℕ) : ℂ :=
  iteratedDeriv d f 0 / (d.factorial:ℂ)

/-- After the lower Taylor coefficients cancel, the normalized second
correction is the next surviving coefficient. The analytic remainder is
retained through the division by the vanishing radial step. -/
theorem analytic_second_coefficient_tendsto {f : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (D : ℕ)
    (hzero : ∀ d < D, taylorCoefficient f d = 0)
    (hnext : taylorCoefficient f (D+1) = 0) :
    Tendsto (fun k : ℕ => ((k:ℂ)+1)^2 *
      (f (canonicalGreenJetStep k) / canonicalGreenJetStep k^D - taylorCoefficient f D))
      atTop (nhds (taylorCoefficient f (D+2))) := by
  obtain ⟨R,hR,he⟩ := hf.exists_eventuallyEq_sum_add_pow_mul (D+3)
  have hsum (z : ℂ) : (∑ d ∈ Finset.range (D+3),
      z^d/(d.factorial:ℂ)*iteratedDeriv d f 0) =
      taylorCoefficient f D*z^D + taylorCoefficient f (D+2)*z^(D+2) := by
    have hlower : (∑ d ∈ Finset.range D,
        z^d/(d.factorial:ℂ)*iteratedDeriv d f 0) = 0 := by
      apply Finset.sum_eq_zero
      intro d hd
      have hc := hzero d (Finset.mem_range.mp hd)
      have hx : z^d/(d.factorial:ℂ)*iteratedDeriv d f 0 = taylorCoefficient f d*z^d := by
        unfold taylorCoefficient
        ring
      rw [hx,hc,zero_mul]
    rw [show D+3=(D+2)+1 by omega, Finset.sum_range_succ,
      show D+2=(D+1)+1 by omega, Finset.sum_range_succ, Finset.sum_range_succ, hlower]
    have hx : z^(D+1)/((D+1).factorial:ℂ)*iteratedDeriv (D+1) f 0 =
        taylorCoefficient f (D+1)*z^(D+1) := by unfold taylorCoefficient; ring
    rw [hx,hnext]
    unfold taylorCoefficient
    ring
  have ht := canonicalGreenJetStep_tendsto_zero
  have hr := hR.continuousAt.tendsto.comp ht
  have hlimit := (tendsto_const_nhds (x := taylorCoefficient f (D+2))).add (ht.mul hr)
  have hlimit' : Tendsto (fun k => taylorCoefficient f (D+2) +
      canonicalGreenJetStep k*R (canonicalGreenJetStep k)) atTop
      (nhds (taylorCoefficient f (D+2))) := by simpa using hlimit
  apply hlimit'.congr'
  filter_upwards [ht.eventually he] with k hk
  simp only [smul_eq_mul] at hk
  rw [hk,hsum]
  have hK : (k:ℂ)+1 ≠ 0 := by
    exact_mod_cast (show (k:ℝ)+1 ≠ 0 by positivity)
  unfold canonicalGreenJetStep
  rw [pow_add, pow_add]
  field_simp
  ring

end
end CarryAllOrderCorrection
