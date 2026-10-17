import GeometryOfNumbers.Analysis.CarryMaterialResidualPositiveTransport

/-! The first-moment null sector of the SAME completed material source.
The second reduction is compared with the preexisting native chain externally.
All finite ordered crossings and the complete new residual are retained. -/
namespace GeometryOfNumbers.Analysis
open Filter
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def carryMaterialSecondAxis : ℝ → ℂ := dslope carryMaterialReducedResponse 0

def carryMaterialSecondScale : ℝ := (carryMaterialSecondAxis 0).re

def carryMaterialSecondReducedResponse (t : ℝ) : ℂ :=
  dslope carryMaterialSecondAxis 0 t /
    ((carryMaterialSecondScale : ℂ)*carryMaterialSecondAxis t)

def carryMaterialSecondAmplitudeCore (t : ℝ) : ℂ :=
  carryMaterialResponseAxis t*carryMaterialSecondAxis t

def carryMaterialSecondChannelCore (t : ℝ) : ℂ :=
  carryMaterialSecondAmplitudeCore t/(Real.sqrt carryMaterialSecondScale : ℂ)

def carryMaterialSecondPositiveChannel (t : ℝ) : ℂ :=
  carryMaterialNormalizedResponse t*carryMaterialSecondAxis t /
    (Real.sqrt carryMaterialSecondScale : ℂ)

def carryMaterialSecondResidualCore (t u : ℝ) : ℝ :=
  (conj (carryMaterialSecondAmplitudeCore t)*carryMaterialSecondAmplitudeCore u*
    dslope carryMaterialSecondReducedResponse t u).re

/-- Exact synthesized remainder of the extracted second channel. -/
def carryMaterialSecondNullSynthesis {n : ℕ} (c a : Fin n → ℝ) (e : ℝ) : ℂ :=
  ∑ i, (c i : ℂ)*(a i : ℂ)^2*dslope carryMaterialSecondChannelCore 0 (e*a i)

def carryMaterialSecondNullEnergy {n : ℕ} (c a : Fin n → ℝ) (e : ℝ) : ℝ :=
  ‖carryMaterialSecondNullSynthesis c a e‖^2 +
    ∑ i, ∑ j, c i*c j*(a i)^2*(a j)^2*
      carryMaterialSecondResidualCore (e*a i) (e*a j)

theorem carryMaterialSecondPositiveChannel_factor
    (h0 : carryMaterialNormalizedResponse 0 = 0) (t : ℝ) :
    carryMaterialSecondPositiveChannel t = (t : ℂ)*carryMaterialSecondChannelCore t := by
  have he := sub_smul_dslope carryMaterialNormalizedResponse 0 t
  have hr : carryMaterialNormalizedResponse t = (t : ℂ)*carryMaterialResponseAxis t := by
    simpa only [sub_zero, h0, Complex.real_smul, carryMaterialResponseAxis] using he.symm
  simp only [carryMaterialSecondPositiveChannel, carryMaterialSecondChannelCore,
    carryMaterialSecondAmplitudeCore, hr]
  ring

theorem carryMaterialSecondAmplitude_factor
    (h0 : carryMaterialNormalizedResponse 0 = 0)
    (h1 : carryMaterialReducedResponse 0 = 0) (t : ℝ) :
    carryMaterialNormalizedResponse t*carryMaterialReducedResponse t =
      (t : ℂ)^2*carryMaterialSecondAmplitudeCore t := by
  have hf (f : ℝ → ℂ) (hz : f 0 = 0) : f t = (t : ℂ)*dslope f 0 t := by
    have h := sub_smul_dslope f 0 t
    simpa only [sub_zero, hz, Complex.real_smul] using h.symm
  rw [hf _ h0, hf _ h1]
  simp only [carryMaterialSecondAmplitudeCore, carryMaterialResponseAxis, carryMaterialSecondAxis]
  ring

/-- Exact cancellation of only the first material moment. -/
theorem carryMaterialSecondChannel_null_synthesis
    (h0 : carryMaterialNormalizedResponse 0 = 0) {n : ℕ} (c a : Fin n → ℝ)
    (hc : (∑ i, c i*a i) = 0) (e : ℝ) :
    (∑ i, (c i : ℂ)*carryMaterialSecondPositiveChannel (e*a i)) =
      (e : ℂ)^2*carryMaterialSecondNullSynthesis c a e := by
  have hh (t : ℝ) : carryMaterialSecondChannelCore t = carryMaterialSecondChannelCore 0 +
      (t : ℂ)*dslope carryMaterialSecondChannelCore 0 t := by
    have h := sub_smul_dslope carryMaterialSecondChannelCore 0 t
    simp only [sub_zero, Complex.real_smul] at h
    linear_combination -h
  have hz : (∑ i, (c i : ℂ)*(a i : ℂ)) = 0 := by exact_mod_cast hc
  have hexp (t : ℝ) : carryMaterialSecondPositiveChannel t =
      (t : ℂ)*carryMaterialSecondChannelCore 0 +
        (t : ℂ)^2*dslope carryMaterialSecondChannelCore 0 t := by
    rw [carryMaterialSecondPositiveChannel_factor h0, hh t]
    ring
  simp_rw [hexp]
  unfold carryMaterialSecondNullSynthesis
  push_cast
  calc
    _ = (e : ℂ)*carryMaterialSecondChannelCore 0*(∑ i, (c i : ℂ)*(a i : ℂ)) +
        (e : ℂ)^2*∑ i, (c i : ℂ)*(a i : ℂ)^2*
          dslope carryMaterialSecondChannelCore 0 (e*a i) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [hz]; ring

private theorem real_complex_feature_energy {n : ℕ} (c : Fin n → ℝ) (v : Fin n → ℂ) :
    ∑ i, ∑ j, c i*c j*(conj (v i)*v j).re = ‖∑ i, (c i : ℂ)*v i‖^2 := by
  have hGram : ((‖∑ i, (c i : ℂ)*v i‖^2 : ℝ) : ℂ) =
      ∑ i, ∑ j, ((c i*c j : ℝ) : ℂ)*(conj (v i)*v j) := by
    rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
    simp only [map_sum, map_mul, Complex.conj_ofReal, Finset.mul_sum, Finset.sum_mul]
    conv_lhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    push_cast
    ring
  have h := congrArg Complex.re hGram.symm
  simpa only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero] using h

theorem carryMaterialSecondResidual_finite_energy {U : Set ℝ}
    (hs : ∀ t ∈ U, ∀ u ∈ U, carryMaterialRealResidual t u =
      (conj (carryMaterialSecondPositiveChannel t)*carryMaterialSecondPositiveChannel u).re +
        t^2*u^2*carryMaterialSecondResidualCore t u)
    {n : ℕ} (c t : Fin n → ℝ) (ht : ∀ i, t i ∈ U) :
    carryRealKernelEnergy carryMaterialRealResidual c t =
      ‖∑ i, (c i : ℂ)*carryMaterialSecondPositiveChannel (t i)‖^2 +
        ∑ i, ∑ j, c i*c j*(t i)^2*(t j)^2*carryMaterialSecondResidualCore (t i) (t j) := by
  rw [← real_complex_feature_energy]
  unfold carryRealKernelEnergy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [hs _ (ht i) _ (ht j)]
  ring

/-- No division by the scale, and no discarded residual. -/
theorem carryMaterialSecondNull_energy_factor {U : Set ℝ}
    (hs : ∀ t ∈ U, ∀ u ∈ U, carryMaterialRealResidual t u =
      (conj (carryMaterialSecondPositiveChannel t)*carryMaterialSecondPositiveChannel u).re +
        t^2*u^2*carryMaterialSecondResidualCore t u)
    (h0 : carryMaterialNormalizedResponse 0 = 0)
    {n : ℕ} (c a : Fin n → ℝ) (hc : (∑ i, c i*a i) = 0) (e : ℝ)
    (ht : ∀ i, e*a i ∈ U) :
    carryRealKernelEnergy carryMaterialRealResidual c (fun i => e*a i) =
      e^4*carryMaterialSecondNullEnergy c a e := by
  rw [carryMaterialSecondResidual_finite_energy hs c _ ht,
    carryMaterialSecondChannel_null_synthesis h0 c a hc]
  have hn : ‖(e : ℂ)^2*carryMaterialSecondNullSynthesis c a e‖^2 =
      e^4*‖carryMaterialSecondNullSynthesis c a e‖^2 := by
    rw [norm_mul, norm_pow, mul_pow, Complex.norm_real, Real.norm_eq_abs]
    have heabs : |e|^4 = e^4 := by
      calc
        _ = (|e|^2)^2 := by ring
        _ = (e^2)^2 := by rw [sq_abs]
        _ = _ := by ring
    simpa only [← pow_mul] using congrArg (fun x => x*‖carryMaterialSecondNullSynthesis c a e‖^2) heabs
  rw [hn]
  unfold carryMaterialSecondNullEnergy
  rw [mul_add]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem carryMaterialSecondNullEnergy_zero
    (hd : deriv carryMaterialSecondChannelCore 0 = 0) {n : ℕ} (c a : Fin n → ℝ) :
    carryMaterialSecondNullEnergy c a 0 =
      carryMaterialSecondResidualCore 0 0*(∑ i, c i*(a i)^2)^2 := by
  unfold carryMaterialSecondNullEnergy carryMaterialSecondNullSynthesis
  simp only [zero_mul, dslope_same, hd, mul_zero, Finset.sum_const_zero, norm_zero,
    zero_pow (by decide : 2 ≠ 0), zero_add]
  rw [pow_two, Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem carryMaterialSecondNullEnergy_continuous
    (hL : ContinuousAt carryMaterialSecondAmplitudeCore 0)
    (hH : DifferentiableAt ℝ carryMaterialSecondChannelCore 0)
    (hz : carryMaterialSecondReducedResponse 0 = 0)
    (hf : DifferentiableAt ℝ carryMaterialSecondReducedResponse 0)
    (hd : ContinuousAt (deriv carryMaterialSecondReducedResponse) 0)
    {n : ℕ} (c a : Fin n → ℝ) : ContinuousAt (carryMaterialSecondNullEnergy c a) 0 := by
  have hD : ContinuousAt (dslope carryMaterialSecondChannelCore 0) 0 :=
    continuousAt_dslope_same.mpr hH
  have hs : ContinuousAt (carryMaterialSecondNullSynthesis c a) 0 := by
    unfold carryMaterialSecondNullSynthesis
    apply tendsto_finsetSum
    intro i _
    have hh : ContinuousAt (fun e : ℝ => dslope carryMaterialSecondChannelCore 0 (e*a i)) 0 :=
      (show ContinuousAt (dslope carryMaterialSecondChannelCore 0) ((0 : ℝ)*a i) by
        simpa only [zero_mul] using hD).comp' (f := fun e : ℝ => e*a i) (x := 0)
          (continuousAt_id.mul_const (a i))
    exact continuousAt_const.mul hh
  have hC (x y : ℝ) :
      ContinuousAt (fun e : ℝ => carryMaterialSecondResidualCore (e*x) (e*y)) 0 := by
    have hx : ContinuousAt (fun e : ℝ => carryMaterialSecondAmplitudeCore (e*x)) 0 :=
      (show ContinuousAt carryMaterialSecondAmplitudeCore ((0 : ℝ)*x) by
        simpa only [zero_mul] using hL).comp' (f := fun e : ℝ => e*x) (x := 0)
          (continuousAt_id.mul_const x)
    have hy : ContinuousAt (fun e : ℝ => carryMaterialSecondAmplitudeCore (e*y)) 0 :=
      (show ContinuousAt carryMaterialSecondAmplitudeCore ((0 : ℝ)*y) by
        simpa only [zero_mul] using hL).comp' (f := fun e : ℝ => e*y) (x := 0)
          (continuousAt_id.mul_const y)
    exact Complex.continuous_re.continuousAt.comp'
      (((Complex.continuous_conj.continuousAt.comp' hx).mul hy).mul
        (carryReal_scaledSlope_continuous carryMaterialSecondReducedResponse hz hf hd x y))
  have hr : ContinuousAt (fun e : ℝ =>
      ∑ i, ∑ j, c i*c j*(a i)^2*(a j)^2*
        carryMaterialSecondResidualCore (e*a i) (e*a j)) 0 := by
    apply tendsto_finsetSum
    intro i _
    apply tendsto_finsetSum
    intro j _
    exact continuousAt_const.mul (hC (a i) (a j))
  exact (hs.norm.pow 2).add hr

/-- Arbitrary fixed family in the first-moment null sector. The complete
new residual is controlled locally by its certified central source scale. -/
theorem carryMaterialSecondNull_fixed_family_pos {U : Set ℝ} (hU : U ∈ nhds 0)
    (hs : ∀ t ∈ U, ∀ u ∈ U, carryMaterialRealResidual t u =
      (conj (carryMaterialSecondPositiveChannel t)*carryMaterialSecondPositiveChannel u).re +
        t^2*u^2*carryMaterialSecondResidualCore t u)
    (h0 : carryMaterialNormalizedResponse 0 = 0)
    (hL : ContinuousAt carryMaterialSecondAmplitudeCore 0)
    (hH : DifferentiableAt ℝ carryMaterialSecondChannelCore 0)
    (hHd : deriv carryMaterialSecondChannelCore 0 = 0)
    (hz : carryMaterialSecondReducedResponse 0 = 0)
    (hf : DifferentiableAt ℝ carryMaterialSecondReducedResponse 0)
    (hd : ContinuousAt (deriv carryMaterialSecondReducedResponse) 0)
    (hp : 0 < carryMaterialSecondResidualCore 0 0)
    {n : ℕ} (c a : Fin n → ℝ)
    (hc : (∑ i, c i*a i) = 0) (hm : (∑ i, c i*(a i)^2) ≠ 0) :
    ∀ᶠ e : ℝ in nhds 0, e ≠ 0 →
      0 < carryRealKernelEnergy carryMaterialRealResidual c (fun i => e*a i) := by
  have hq := carryMaterialSecondNullEnergy_continuous hL hH hz hf hd c a
  have hpos : 0 < carryMaterialSecondNullEnergy c a 0 := by
    rw [carryMaterialSecondNullEnergy_zero hHd]
    exact mul_pos hp (sq_pos_of_ne_zero hm)
  have hqp := (tendsto_order.1 hq).1 0 hpos
  have hmem : ∀ᶠ e : ℝ in nhds 0, ∀ i, e*a i ∈ U := by
    apply Filter.eventually_all.mpr
    intro i
    have he : Tendsto (fun e : ℝ => e*a i) (nhds 0) (nhds 0) := by
      simpa only [id_eq, zero_mul] using (continuousAt_id.mul_const (a i)).tendsto (x := (0 : ℝ))
    exact he.eventually hU
  filter_upwards [hqp, hmem] with e he hm hne
  rw [carryMaterialSecondNull_energy_factor hs h0 c a hc e hm]
  have hp4 : 0 < e^4 := by
    simpa only [← pow_mul] using sq_pos_of_pos (sq_pos_of_ne_zero hne)
  exact mul_pos hp4 he

end
end GeometryOfNumbers.Analysis
