import CriticalTail

/-! Quantitative control of ALL THREE ordered remainder terms in the same
PR58 reduced Green balance. The magnitude is an error envelope only; no
physical inner product, source or domain is replaced. -/
namespace CarryCellTail
open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.BaseTwoCompletion
open CarryMaterialParts Filter Topology
open scoped BigOperators ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem reciprocal_cell_summable (M : ℕ) :
    Summable (fun k : ℕ => (1:ℝ)/((4*(k+M)+3:ℕ):ℝ)^2) :=
  (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2:ℕ))).comp_injective
    (by intro i j h; dsimp at h; omega)

theorem bounded_cell_series_tail (f : ℕ → ℂ) (hf : Summable (fun k => ‖f k‖))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ k, ‖f k‖ ≤ C/((4*k+3:ℕ):ℝ)^2)
    (M : ℕ) (hM : 0 < M) :
    ‖(∑' k, f k)-(∑ k ∈ Finset.range M, f k)‖ ≤ C/(4*(4*(M:ℝ)-1)) := by
  rw [← hf.of_norm.sum_add_tsum_nat_add M, add_sub_cancel_left]
  apply (norm_tsum_le_tsum_norm (hf.comp_injective (by intro i j h; exact Nat.add_right_cancel h))).trans
  calc
    ∑' k, ‖f (k+M)‖ ≤ ∑' k, C*((1:ℝ)/((4*(k+M)+3:ℕ):ℝ)^2) :=
      (hf.comp_injective (by intro i j h; exact Nat.add_right_cancel h)).tsum_le_tsum
        (fun k => by simpa only [mul_one_div] using hb (k+M)) ((reciprocal_cell_summable M).mul_left C)
    _ = C*(∑' k : ℕ, (1:ℝ)/((4*(k+M)+3:ℕ):ℝ)^2) := tsum_mul_left
    _ ≤ C/(4*(4*(M:ℝ)-1)) := by
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left (reciprocal_cell_tail M hM) hC

theorem clock_cell_point_bound (k : ℕ) (t : ℝ) (ht : |t| ≤ (1/4:ℝ)) :
    ‖clockCell k t‖ ≤ 8/((4*k+3:ℕ):ℝ)^2 := by
  rw [← complex_clock_real, norm_mul, Complex.norm_I, one_mul]
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (c:=(t:ℂ)) (f:=complexCell k) (by norm_num : (0:ℝ) < 1/4)
    (complex_cell_entire k).diffContOnCl (by
      intro w hw
      have hd : ‖w-(t:ℂ)‖ = (1/4:ℝ) := by simpa only [Metric.mem_sphere, dist_eq_norm] using hw
      apply complex_cell_bound k w
      have hnorm := norm_add_le (w-(t:ℂ)) (t:ℂ)
      rw [sub_add_cancel] at hnorm
      simp only [Complex.norm_real, Real.norm_eq_abs] at hnorm
      linarith)
  convert h using 1
  ring

theorem ordinary_tail_point_bound (M : ℕ) (hM : 0 < M) (t : ℝ) (ht : |t| ≤ (1/4:ℝ)) :
    ‖ordinaryTail M t‖ ≤ 2/(4*(4*(M:ℝ)-1)) := by
  have he : baseTwoCompletedBoundaryValue t = ∑' k, baseTwoCriticalCenterCell t k := by
    simp only [baseTwoCompletedBoundaryValue, baseTwoCriticalCenterCell_eq_gradientEdges]
  rw [ordinaryTail, he]
  apply bounded_cell_series_tail _ (summable_norm_baseTwoCriticalCenterCell t) 2 (by norm_num)
    (fun k => ?_) M hM
  rw [← complex_cell_real k t]
  exact complex_cell_bound k (t:ℂ) (by simpa only [Complex.norm_real, Real.norm_eq_abs] using ht.trans (by norm_num : (1/4:ℝ) ≤ 1/2))

theorem clock_tail_point_bound (M : ℕ) (hM : 0 < M) (t : ℝ) (ht : |t| ≤ (1/4:ℝ)) :
    ‖clockTail M t‖ ≤ 8/(4*(4*(M:ℝ)-1)) := by
  have he : carryValveKappa t = ∑' k, clockCell k t := by
    rw [← cellReturnReadout_clock_source t, cellReturnReadout_apply]
    rfl
  have hs : Summable (fun k => ‖clockCell k t‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun k => by simpa only [mul_one_div] using clock_cell_point_bound k t ht)
      ((reciprocal_cell_summable 0).mul_left 8 |>.congr (by intro k; simp [div_eq_mul_inv]))
  rw [clockTail, he]
  exact bounded_cell_series_tail _ hs 8 (by norm_num) (fun k => clock_cell_point_bound k t ht) M hM

/-- Coordinate magnitude used ONLY to upper-bound errors. -/
def pairMagnitude (x : ℂ × ℂ) : ℝ := ‖x.1‖+‖x.2‖
def balanceMagnitude (t u : ℝ) : ℝ :=
  |carryMaterialResponseScale^2*t*u|+|carryMaterialResponseScale*(u-t)|/2

theorem reduced_form_norm_bound (t u : ℝ) (x y : ℂ × ℂ) :
    ‖reducedCellForm t u x y‖ ≤ balanceMagnitude t u*pairMagnitude x*pairMagnitude y := by
  have hgreen : ‖carryMaterialPairGreen x y‖ ≤ ‖x.2‖*‖y.1‖+‖x.1‖*‖y.2‖ := by
    simpa only [carryMaterialPairGreen, RCLike.inner_apply, norm_mul, Complex.norm_conj, mul_comm] using
      norm_sub_le (y.1*conj x.2) (y.2*conj x.1)
  have h := norm_sub_le
    (((carryMaterialResponseScale^2*t*u:ℝ):ℂ)*carryMaterialPairGreen x y)
    ((((carryMaterialResponseScale*(u-t):ℝ):ℂ)/2)*conj x.1*y.1)
  simp only [norm_mul, norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat, ← abs_mul] at h
  apply h.trans
  have h1 : (0:ℝ) ≤ |carryMaterialResponseScale^2*t*u| := abs_nonneg _
  have h2 : (0:ℝ) ≤ |carryMaterialResponseScale*(u-t)|/2 := by positivity
  have hg : ‖carryMaterialPairGreen x y‖ ≤ pairMagnitude x*pairMagnitude y := by
    unfold pairMagnitude
    nlinarith [norm_nonneg x.1, norm_nonneg x.2, norm_nonneg y.1, norm_nonneg y.2,
      mul_nonneg (norm_nonneg x.1) (norm_nonneg y.1),
      mul_nonneg (norm_nonneg x.2) (norm_nonneg y.2)]
  have hc : ‖x.1‖*‖y.1‖ ≤ pairMagnitude x*pairMagnitude y :=
    mul_le_mul (le_add_of_nonneg_right (norm_nonneg _))
      (le_add_of_nonneg_right (norm_nonneg _)) (norm_nonneg _)
      (add_nonneg (norm_nonneg _) (norm_nonneg _))
  calc
    _ ≤ |carryMaterialResponseScale^2*t*u| *(pairMagnitude x*pairMagnitude y)+
        (|carryMaterialResponseScale*(u-t)|/2)*(pairMagnitude x*pairMagnitude y) := by
      calc
        _ = |carryMaterialResponseScale^2*t*u| *‖carryMaterialPairGreen x y‖+
          (|carryMaterialResponseScale*(u-t)|/2)*(‖x.1‖*‖y.1‖) := by ring
        _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hg h1) (mul_le_mul_of_nonneg_left hc h2)
    _ = _ := by unfold balanceMagnitude; ring

def pairTailBudget (M : ℕ) (t : ℝ) : ℝ :=
  (10*‖baseTwoCanonicalDressingScalar t‖+2*‖deriv baseTwoCanonicalDressingScalar t‖)/
    (4*(4*(M:ℝ)-1))

theorem native_tail_pair_exact (eta : ℝ) (heta : eta ≠ 0) (M : ℕ) (t : ℝ) :
    carryValveTailPair eta M t =
      (Complex.I*baseTwoCanonicalDressingScalar t*clockTail M t-
        deriv baseTwoCanonicalDressingScalar t*ordinaryTail M t,
       baseTwoCanonicalDressingScalar t*ordinaryTail M t) := by
  have hp : carryValveReturnPrefix eta (baseTwoCompletedBoundaryHilbertState t) M = ordinaryHead M t := by
    simp only [carryValveReturnPrefix, ordinaryHead,
      carryValveCell_source eta heta]
  have hk : carryValveReturnPrefix eta (completedBoundaryTransportedClock (carryValveSource t)) M = clockHead M t := by
    simp only [carryValveReturnPrefix, clockHead, carryValveCell_eq eta heta]
    rfl
  unfold carryValveTailPair carryValveCompanionTail carryValveValueTail carryValveReturnTail
  change (Complex.I*baseTwoCanonicalDressingScalar t*(carryValveKappa t-_)-
    deriv baseTwoCanonicalDressingScalar t*(baseTwoCompletedBoundaryValue t-_),
    baseTwoCanonicalDressingScalar t*(baseTwoCompletedBoundaryValue t-_)) = _
  rw [hp, hk]
  rfl

theorem native_tail_pair_bound (eta : ℝ) (heta : eta ≠ 0) (M : ℕ) (hM : 0 < M)
    (t : ℝ) (ht : |t| ≤ (1/4:ℝ)) :
    pairMagnitude (carryValveTailPair eta M t) ≤ pairTailBudget M t := by
  rw [native_tail_pair_exact eta heta]
  have hb := ordinary_tail_point_bound M hM t ht
  have hk := clock_tail_point_bound M hM t ht
  have h := norm_sub_le (Complex.I*baseTwoCanonicalDressingScalar t*clockTail M t)
    (deriv baseTwoCanonicalDressingScalar t*ordinaryTail M t)
  simp only [norm_mul, Complex.norm_I, one_mul] at h
  unfold pairMagnitude pairTailBudget
  dsimp only [Prod.fst, Prod.snd]
  rw [norm_mul]
  calc
    _ ≤ ‖baseTwoCanonicalDressingScalar t‖*‖clockTail M t‖+
      ‖deriv baseTwoCanonicalDressingScalar t‖*‖ordinaryTail M t‖+
      ‖baseTwoCanonicalDressingScalar t‖*‖ordinaryTail M t‖ := by linarith
    _ ≤ ‖baseTwoCanonicalDressingScalar t‖*(8/(4*(4*(M:ℝ)-1)))+
      ‖deriv baseTwoCanonicalDressingScalar t‖*(2/(4*(4*(M:ℝ)-1)))+
      ‖baseTwoCanonicalDressingScalar t‖*(2/(4*(4*(M:ℝ)-1))) := by gcongr
    _ = _ := by ring

/-- HT, TH and TT separately survive with their original signed form. -/
theorem full_green_tail_budget (eta : ℝ) (heta : eta ≠ 0) (M L : ℕ)
    (hM : 0 < M) (hL : 0 < L) (t u : ℝ) (ht : |t| ≤ (1/4:ℝ)) (hu : |u| ≤ (1/4:ℝ)) :
    ‖carryValveReducedReturnBalance eta t u-carryValvePrefixReducedBalance eta M L t u‖ ≤
      balanceMagnitude t u*(
        pairMagnitude (carryValvePrefixPair eta M t)*pairTailBudget L u+
        pairTailBudget M t*pairMagnitude (carryValvePrefixPair eta L u)+
        pairTailBudget M t*pairTailBudget L u) := by
  rw [reduced_return_tail_defect eta heta]
  have h := (norm_add_le
    (reducedCellForm t u (carryValvePrefixPair eta M t) (carryValveTailPair eta L u)+
      reducedCellForm t u (carryValveTailPair eta M t) (carryValvePrefixPair eta L u))
    (reducedCellForm t u (carryValveTailPair eta M t) (carryValveTailPair eta L u))).trans
    (add_le_add (norm_add_le _ _) (le_refl _))
  apply h.trans
  have hht := reduced_form_norm_bound t u (carryValvePrefixPair eta M t) (carryValveTailPair eta L u)
  have hth := reduced_form_norm_bound t u (carryValveTailPair eta M t) (carryValvePrefixPair eta L u)
  have htt := reduced_form_norm_bound t u (carryValveTailPair eta M t) (carryValveTailPair eta L u)
  have hb := native_tail_pair_bound eta heta M hM t ht
  have hc := native_tail_pair_bound eta heta L hL u hu
  have hp (x : ℂ × ℂ) : 0 ≤ pairMagnitude x := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hk : 0 ≤ balanceMagnitude t u := by unfold balanceMagnitude; positivity
  have he : 0 ≤ pairTailBudget M t := (hp _).trans hb
  have hf : 0 ≤ pairTailBudget L u := (hp _).trans hc
  calc
    _ ≤ balanceMagnitude t u*pairMagnitude (carryValvePrefixPair eta M t)*pairMagnitude (carryValveTailPair eta L u)+
        balanceMagnitude t u*pairMagnitude (carryValveTailPair eta M t)*pairMagnitude (carryValvePrefixPair eta L u)+
        balanceMagnitude t u*pairMagnitude (carryValveTailPair eta M t)*pairMagnitude (carryValveTailPair eta L u) :=
      add_le_add (add_le_add hht hth) htt
    _ ≤ _ := by
      nlinarith [mul_le_mul_of_nonneg_left hc (mul_nonneg hk (hp (carryValvePrefixPair eta M t))),
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hk) (hp (carryValvePrefixPair eta L u)),
        mul_le_mul (mul_le_mul_of_nonneg_left hb hk) hc (hp _) (mul_nonneg hk he)]
end
end CarryCellTail
