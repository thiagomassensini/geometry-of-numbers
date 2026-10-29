import ClockTails

namespace CarryCellTail
open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.BaseTwoCompletion
open CarryMaterialParts Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

def rJet (n : ℕ) (f : ℝ → ℂ) : ℂ := carryScalarJetShift n f 0

theorem rJet_derivative {f : ℝ → ℂ} (hf : AnalyticAt ℝ f 0) (n : ℕ) :
    rJet n f = iteratedDeriv n f 0/(n.factorial:ℂ) := by
  obtain ⟨p,hp⟩ := hf
  have hc := (hp.has_fpower_series_iterate_dslope_fslope n).coeff_zero (fun _ => 1)
  change ((FormalMultilinearSeries.fslope^[n]) p).coeff 0 = _ at hc
  rw [FormalMultilinearSeries.coeff_iterate_fslope, zero_add] at hc
  change p.coeff n = rJet n f at hc
  obtain ⟨radius,hball⟩ := hp
  have hd := hball.factorial_smul (1:ℝ) n
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod] at hd
  simp only [FormalMultilinearSeries.apply_eq_prod_smul_coeff, Finset.prod_const_one,
    one_smul, nsmul_eq_mul] at hd
  rw [← hc, eq_div_iff (by exact_mod_cast Nat.factorial_ne_zero n)]
  simpa only [mul_comm] using hd

theorem rJet_add {f g : ℝ → ℂ} (hf : AnalyticAt ℝ f 0) (hg : AnalyticAt ℝ g 0) (n : ℕ) :
    rJet n (fun t => f t+g t) = rJet n f+rJet n g := by
  change rJet n (f+g) = _
  rw [rJet_derivative (hf.add hg), rJet_derivative hf, rJet_derivative hg,
    iteratedDeriv_add (hf.contDiffAt) (hg.contDiffAt)]
  ring

theorem rJet_sub {f g : ℝ → ℂ} (hf : AnalyticAt ℝ f 0) (hg : AnalyticAt ℝ g 0) (n : ℕ) :
    rJet n (fun t => f t-g t) = rJet n f-rJet n g := by
  change rJet n (f-g) = _
  rw [rJet_derivative (hf.sub hg), rJet_derivative hf, rJet_derivative hg,
    iteratedDeriv_sub (hf.contDiffAt) (hg.contDiffAt)]
  ring

/-- The original normalized Taylor product, with every coefficient retained. -/
theorem rJet_mul {f g : ℝ → ℂ} (hf : AnalyticAt ℝ f 0) (hg : AnalyticAt ℝ g 0) (n : ℕ) :
    rJet n (fun t => f t*g t) =
      ∑ j ∈ Finset.range (n+1), rJet j f*rJet (n-j) g := by
  change rJet n (f*g) = _
  rw [rJet_derivative (hf.mul hg),
    iteratedDeriv_mul (hf.contDiffAt) (hg.contDiffAt),
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  rw [rJet_derivative hf, rJet_derivative hg, Nat.cast_choose ℂ (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
  have hn : (n.factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hj0 : (j.factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hnj : ((n-j).factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n-j)
  field_simp

/-- A quantitative budget for a finite convolution, not a positivity claim. -/
theorem rJet_mul_bound {f g : ℝ → ℂ} (hf : AnalyticAt ℝ f 0) (hg : AnalyticAt ℝ g 0)
    (E : ℕ → ℝ) (hE : ∀ j, ‖rJet j g‖ ≤ E j) (n : ℕ) :
    ‖rJet n (fun t => f t*g t)‖ ≤
      ∑ j ∈ Finset.range (n+1), ‖rJet j f‖*E (n-j) := by
  rw [rJet_mul hf hg]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hE _) (norm_nonneg _)

theorem rJet_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ)
    (hf : ∀ i ∈ s, AnalyticAt ℝ (f i) 0) (n : ℕ) :
    rJet n (fun t => ∑ i ∈ s, f i t) = ∑ i ∈ s, rJet n (f i) := by
  have hs := s.analyticAt_fun_sum hf
  rw [rJet_derivative hs, iteratedDeriv_fun_sum (fun i hi => (hf i hi).contDiffAt), Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  rw [rJet_derivative (hf i hi)]
end
end CarryCellTail
