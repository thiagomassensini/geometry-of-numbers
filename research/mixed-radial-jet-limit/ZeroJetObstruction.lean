import MixedRadialLimits

/-! The only sign input is the independently established first native moment.
No all-order Hankel sign, contractivity or new source is assumed. -/
namespace CarryMixedRadial
open CarrySelfAdjointOperator CarryCompletedTrace Filter Topology
open scoped ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false

theorem doubled_limit_ne_diagonal :
    (((3*Real.sqrt 2/4 : ℝ) : ℂ)*(canonicalCompletedNativeLogDerivativeMoment 0 : ℂ)) ≠
      (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := by
  intro h
  have he : (3*Real.sqrt 2/4)*canonicalCompletedNativeLogDerivativeMoment 0 =
      canonicalCompletedNativeLogDerivativeMoment 0 := by exact_mod_cast h
  have hm := canonicalCompletedNativeLogDerivativeMoment_zero_pos
  have hr := doubled_zero_factor_gt_one
  nlinarith

/-- Diagonal convergence cannot be promoted to a two-index limit in the
unchanged original carrier. Both paths go to infinity in BOTH coordinates. -/
theorem no_joint_zero_limit : ¬ ∃ L : ℂ,
    Tendsto (fun p : ℕ × ℕ => zeroPairing p.1 p.2) atTop (nhds L) := by
  rintro ⟨L,hL⟩
  have hd := hL.comp (tendsto_atTop_diagonal : Tendsto (fun k : ℕ => (k,k)) atTop atTop)
  have hpath : Tendsto (fun k : ℕ => (k,2*k+1)) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_id.prodMk doubled_index_tendsto
  have hx := hL.comp hpath
  have h1 := tendsto_nhds_unique hd diagonal_zero_limit
  have h2 := tendsto_nhds_unique hx doubled_zero_limit
  exact doubled_limit_ne_diagonal (h2.symm.trans h1)

/-- An actual difference of two complete source jets has negative signed
balance eventually. The Hilbert norms of its TWO channels remain nonnegative. -/
theorem doubled_difference_negative_eventually :
    ∀ᶠ k : ℕ in atTop, (differencePairing k (2*k+1)).re < 0 := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp doubled_difference_limit
  have hneg : (2-3*Real.sqrt 2/2)*canonicalCompletedNativeLogDerivativeMoment 0 < 0 := by
    have hr := doubled_zero_factor_gt_one
    have hm := canonicalCompletedNativeLogDerivativeMoment_zero_pos
    exact mul_neg_of_neg_of_pos (by linarith) hm
  have hh := Tendsto.eventually_lt h tendsto_const_nhds (by
    simpa using hneg)
  simpa only [Function.comp_def] using hh

/-- Hence the raw union of all radial realizations cannot be a single
positive Hilbert Gram with these same pairings. This is specific to that union. -/
theorem no_hilbert_gram_for_raw_radial_union {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] :
    ¬ ∃ v : ℕ → E, ∀ k l, zeroPairing k l = inner ℂ (v k) (v l) := by
  rintro ⟨v,hv⟩
  obtain ⟨k,hk⟩ := doubled_difference_negative_eventually.exists
  have he : differencePairing k (2*k+1) =
      inner ℂ (v k-v (2*k+1)) (v k-v (2*k+1)) := by
    rw [difference_pairing_four_crosses]
    simp only [hv,inner_sub_left,inner_sub_right]
    ring
  rw [he] at hk
  exact (not_lt_of_ge (inner_self_nonneg (𝕜 := ℂ) (x := v k-v (2*k+1)))) hk


/-- Exact determinant of the limiting two-scale coefficient matrix. -/
theorem doubled_factor_determinant : 1-(3*Real.sqrt 2/4)^2 = (-1/8 : ℝ) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith

end
end CarryMixedRadial
