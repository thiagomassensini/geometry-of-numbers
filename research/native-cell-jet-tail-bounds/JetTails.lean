import CellCauchy

namespace CarryCellTail
open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.BaseTwoCompletion
open CarryMaterialParts Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000

def cshift (n : ℕ) (f : ℂ → ℂ) : ℂ → ℂ := (fun g : ℂ → ℂ => dslope g 0)^[n] f

theorem cshift_analytic {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (n : ℕ) :
    AnalyticAt ℂ (cshift n f) 0 := by
  obtain ⟨p,hp⟩ := hf
  exact (hp.has_fpower_series_iterate_dslope_fslope n).analyticAt

theorem cshift_coefficient {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (n : ℕ) :
    cshift n f 0 = complexJet n f := by
  have h := (hf.hasFPowerSeriesAt.has_fpower_series_iterate_dslope_fslope n).coeff_zero (fun _ => 1)
  change (((FormalMultilinearSeries.fslope)^[n])
    (FormalMultilinearSeries.ofScalars ℂ (fun j => iteratedDeriv j f 0 / (j.factorial:ℂ)))).coeff 0 = _ at h
  rw [FormalMultilinearSeries.coeff_iterate_fslope] at h
  simpa only [zero_add, FormalMultilinearSeries.coeff_ofScalars, complexJet, cshift] using h.symm

theorem real_dslope_germ {f : ℝ → ℂ} {g : ℂ → ℂ}
    (he : f =ᶠ[nhds 0] fun t : ℝ => g (t:ℂ)) (hg : DifferentiableAt ℂ g 0) :
    dslope f 0 =ᶠ[nhds 0] fun t : ℝ => dslope g 0 (t:ℂ) := by
  have hd := hg.hasDerivAt.comp_ofReal.congr_of_eventuallyEq he
  filter_upwards [he] with t ht
  by_cases hz : t = 0
  · subst t; simpa only [Complex.ofReal_zero, dslope_same] using hd.deriv
  · rw [dslope_of_ne f hz, dslope_of_ne g (Complex.ofReal_ne_zero.mpr hz)]
    simp [slope, ht, he.eq_of_nhds, Complex.real_smul]

theorem real_jet_complex {f : ℝ → ℂ} {g : ℂ → ℂ}
    (he : f =ᶠ[nhds 0] fun t : ℝ => g (t:ℂ)) (hg : AnalyticAt ℂ g 0) (n : ℕ) :
    carryScalarJetShift n f 0 = complexJet n g := by
  have hshift : carryScalarJetShift n f =ᶠ[nhds 0] fun t : ℝ => cshift n g (t:ℂ) := by
    induction n with
    | zero => exact he
    | succ n ih =>
      simpa only [carryScalarJetShift_succ, cshift, Function.iterate_succ_apply'] using
        real_dslope_germ ih (cshift_analytic hg n).differentiableAt
  simpa only [Complex.ofReal_zero, cshift_coefficient hg n] using hshift.eq_of_nhds

theorem cell_jet_coefficient (m k : ℕ) : cellJet m k = complexJet m (complexCell k) := by
  rw [cell_jet_source]
  exact real_jet_complex (.of_forall (fun t => (complex_cell_real k t).symm))
    ((complex_cell_entire k).analyticAt 0) m

theorem cell_jet_bound (m k : ℕ) :
    ‖cellJet m k‖ ≤ 2^(m+1) / ((4*k+3:ℕ):ℝ)^2 := by
  rw [cell_jet_coefficient]
  exact complex_jet_bound m k

theorem reciprocal_step (a : ℝ) (ha : 4 < a) :
    1/a^2 ≤ 1/(4*(a-4))-1/(4*a) := by
  have ha0 : 0 < a := by linarith
  have ha4 : a-4 ≠ 0 := by linarith
  have he : 1/(4*(a-4))-1/(4*a) = 1/(a*(a-4)) := by
    field_simp
    ring
  rw [he]
  apply one_div_le_one_div_of_le (by positivity : 0 < a*(a-4))
  nlinarith

/-- A rational telescoping envelope, including every omitted whole cell. -/
theorem reciprocal_cell_tail (M : ℕ) (hM : 0 < M) :
    ∑' k : ℕ, (1:ℝ)/((4*(k+M)+3:ℕ):ℝ)^2 ≤ 1/(4*(4*(M:ℝ)-1)) := by
  have hm : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hm0 : 0 < 4*(4*(M:ℝ)-1) := by linarith
  apply tsum_le_of_sum_le' (le_of_lt (one_div_pos.mpr hm0))
  intro s
  obtain ⟨N,hN⟩ := Finset.exists_nat_subset_range s
  have hsum : ∀ N : ℕ, ∑ k ∈ Finset.range N, (1:ℝ)/((4*(k+M)+3:ℕ):ℝ)^2 ≤
      1/(4*(4*(M:ℝ)-1))-1/(4*(4*(N+M:ℕ)-1)) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have he := reciprocal_step (4*((N:ℝ)+M)+3) (by
        have hn : (0:ℝ) ≤ N := Nat.cast_nonneg N
        linarith)
      push_cast at ih ⊢
      rw [show 4*((N:ℝ)+M)+3-4 = 4*((N:ℝ)+M)-1 by ring] at he
      rw [show 4*((N:ℝ)+1+M)-1 = 4*((N:ℝ)+M)+3 by ring]
      linarith
  have hb := hsum N
  have hc : (0:ℝ) ≤ 1/(4*(4*(N+M:ℕ)-1)) := by
    apply one_div_nonneg.mpr
    push_cast
    linarith [Nat.cast_nonneg (α:=ℝ) N]
  calc
    ∑ k ∈ s, (1:ℝ)/((4*(k+M)+3:ℕ):ℝ)^2 ≤
        ∑ k ∈ Finset.range N, (1:ℝ)/((4*(k+M)+3:ℕ):ℝ)^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hN (fun _ _ _ => by positivity)
    _ ≤ 1/(4*(4*(M:ℝ)-1)) := by linarith

/-- Explicit fixed-order error; no finite positivity certificate occurs. -/
theorem return_jet_quantitative (m M : ℕ) (hM : 0 < M) :
    ‖carryScalarJetShift m baseTwoCompletedBoundaryValue 0-
      (∑ k ∈ Finset.range M, cellJet m k)‖ ≤ 2^(m+1)/(4*(4*(M:ℝ)-1)) := by
  apply (return_jet_tail_bound m M).trans
  have hs : Summable (fun k : ℕ => (1:ℝ)/((4*(k+M)+3:ℕ):ℝ)^2) :=
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2:ℕ))).comp_injective
      (by intro i j h; dsimp at h; omega)
  calc
    ∑' k, ‖cellJet m (k+M)‖ ≤ ∑' k, 2^(m+1) * ((1:ℝ)/((4*(k+M)+3:ℕ):ℝ)^2) :=
      (cell_jet_norm_summable m |>.comp_injective (by intro i j h; exact Nat.add_right_cancel h)).tsum_le_tsum
        (fun k => by simpa only [mul_one_div] using cell_jet_bound m (k+M)) (hs.mul_left _)
    _ = 2^(m+1)*(∑' k : ℕ, (1:ℝ)/((4*(k+M)+3:ℕ):ℝ)^2) := tsum_mul_left
    _ ≤ 2^(m+1)/(4*(4*(M:ℝ)-1)) := by
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left (reciprocal_cell_tail M hM) (by positivity : (0:ℝ) ≤ 2^(m+1))
end
end CarryCellTail
