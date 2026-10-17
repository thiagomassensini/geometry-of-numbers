import GeometryOfNumbers.Analysis.CarryMaterialCompanionGreenTransport

/-! Real finite-energy tests and constructive orthogonal extraction for the
actual material residual. The comparison file supplies the already proved
source split. No existence of a positive realization is assumed here. -/
namespace GeometryOfNumbers.Analysis
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def carryMaterialRealFeature (t : ℝ) : ℝ := (carryMaterialPositiveFeature t).re

def carryMaterialRealKernel (t u : ℝ) : ℝ :=
  (dslope carryMaterialNormalizedResponse t u).re

def carryMaterialRealResidual (t u : ℝ) : ℝ :=
  (star (carryMaterialNormalizedResponse t)*carryMaterialNormalizedResponse u*
    dslope carryMaterialReducedResponse t u).re

def carryRealKernelEnergy (K : ℝ → ℝ → ℝ) {n : ℕ}
    (c : Fin n → ℝ) (t : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, c i*c j*K (t i) (t j)

/-- All finite real tests; no chosen moment matrix or factorization. -/
def CarryRealKernelNonnegativeOn (K : ℝ → ℝ → ℝ) (U : Set ℝ) : Prop :=
  ∀ (n : ℕ) (c : Fin n → ℝ) (t : Fin n → ℝ), (∀ i, t i ∈ U) →
    0 ≤ carryRealKernelEnergy K c t

/-- Add the actual central source as one extra observation. -/
def carryMaterialCenteredCoefficients {n : ℕ} (c : Fin n → ℝ) (t : Fin n → ℝ) :
    Fin (n+1) → ℝ :=
  Fin.cases (-(∑ i, c i*carryMaterialRealFeature (t i))/carryMaterialRealFeature 0) c

def carryMaterialCenteredParameters {n : ℕ} (t : Fin n → ℝ) : Fin (n+1) → ℝ :=
  Fin.cases 0 t

theorem carryMaterialCenteredParameters_mem {U : Set ℝ} (h0 : (0 : ℝ) ∈ U)
    {n : ℕ} (t : Fin n → ℝ) (ht : ∀ i, t i ∈ U) :
    ∀ i, carryMaterialCenteredParameters t i ∈ U := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact h0
  · exact ht j

theorem carryMaterialCenteredCoefficients_cancel
    (hp : carryMaterialRealFeature 0 ≠ 0) {n : ℕ}
    (c : Fin n → ℝ) (t : Fin n → ℝ) :
    ∑ i, carryMaterialCenteredCoefficients c t i *
      carryMaterialRealFeature (carryMaterialCenteredParameters t i) = 0 := by
  rw [Fin.sum_univ_succ]
  simp only [carryMaterialCenteredCoefficients, carryMaterialCenteredParameters,
    Fin.cases_zero, Fin.cases_succ]
  field_simp
  ring

private theorem rank_one_energy (p : ℝ → ℝ) {n : ℕ}
    (c : Fin n → ℝ) (t : Fin n → ℝ) :
    (∑ i, c i*p (t i))^2 = ∑ i, ∑ j, c i*c j*(p (t i)*p (t j)) := by
  rw [pow_two, Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Source identity lifted to every finite family BEFORE sign extraction. -/
theorem carryMaterialReal_energy_split {U : Set ℝ}
    (hs : ∀ t ∈ U, ∀ u ∈ U, carryMaterialRealKernel t u =
      carryMaterialRealFeature t*carryMaterialRealFeature u + carryMaterialRealResidual t u)
    {n : ℕ} (c : Fin n → ℝ) (t : Fin n → ℝ) (ht : ∀ i, t i ∈ U) :
    carryRealKernelEnergy carryMaterialRealKernel c t =
      (∑ i, c i*carryMaterialRealFeature (t i))^2 +
        carryRealKernelEnergy carryMaterialRealResidual c t := by
  rw [rank_one_energy]
  unfold carryRealKernelEnergy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [hs _ (ht i) _ (ht j)]
  ring

/-- The central readout is cancelled, not any mixed residual terms. -/
theorem carryMaterialReal_centered_energy {U : Set ℝ} (h0 : (0 : ℝ) ∈ U)
    (hp : carryMaterialRealFeature 0 ≠ 0)
    (hs : ∀ t ∈ U, ∀ u ∈ U, carryMaterialRealKernel t u =
      carryMaterialRealFeature t*carryMaterialRealFeature u + carryMaterialRealResidual t u)
    (hr0 : ∀ t, carryMaterialRealResidual 0 t = 0)
    (h0r : ∀ t, carryMaterialRealResidual t 0 = 0)
    {n : ℕ} (c : Fin n → ℝ) (t : Fin n → ℝ) (ht : ∀ i, t i ∈ U) :
    carryRealKernelEnergy carryMaterialRealKernel (carryMaterialCenteredCoefficients c t)
      (carryMaterialCenteredParameters t) = carryRealKernelEnergy carryMaterialRealResidual c t := by
  rw [carryMaterialReal_energy_split hs _ _ (carryMaterialCenteredParameters_mem h0 t ht),
    carryMaterialCenteredCoefficients_cancel hp]
  simp only [zero_pow (by decide : 2 ≠ 0), zero_add]
  unfold carryRealKernelEnergy
  rw [Fin.sum_univ_succ]
  simp only [carryMaterialCenteredCoefficients, carryMaterialCenteredParameters,
    Fin.cases_zero, Fin.cases_succ, hr0, mul_zero, Finset.sum_const_zero, zero_add]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_succ]
  simp only [Fin.cases_zero, Fin.cases_succ, h0r, mul_zero, zero_add]

/-- Removing the calibrated center does NOT make the all-family sign a
weaker obligation: one extra genuine source observation reverses the test. -/
theorem carryMaterialReal_nonnegative_iff {U : Set ℝ} (h0 : (0 : ℝ) ∈ U)
    (hp : carryMaterialRealFeature 0 ≠ 0)
    (hs : ∀ t ∈ U, ∀ u ∈ U, carryMaterialRealKernel t u =
      carryMaterialRealFeature t*carryMaterialRealFeature u + carryMaterialRealResidual t u)
    (hr0 : ∀ t, carryMaterialRealResidual 0 t = 0)
    (h0r : ∀ t, carryMaterialRealResidual t 0 = 0) :
    CarryRealKernelNonnegativeOn carryMaterialRealKernel U ↔
      CarryRealKernelNonnegativeOn carryMaterialRealResidual U := by
  constructor
  · intro h n c t ht
    have he := carryMaterialReal_centered_energy h0 hp hs hr0 h0r c t ht
    rw [← he]
    exact h _ _ _ (carryMaterialCenteredParameters_mem h0 t ht)
  · intro h n c t ht
    rw [carryMaterialReal_energy_split hs c t ht]
    exact add_nonneg (sq_nonneg _) (h n c t ht)

/-- Orthogonal extraction in a GIVEN real Hilbert realization. This map
never asserts that such a realization has been constructed. -/
def carryMaterialRealOrthogonalResidual {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (v : ℝ → H) (t : ℝ) : H :=
  v t - (carryMaterialRealFeature t/carryMaterialRealFeature 0) • v 0

/-- Converse assembly uses the inherited direct-sum inner product. -/
def carryMaterialRealKernelLift {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (v : ℝ → H) (t : ℝ) : WithLp 2 (ℝ × H) :=
  WithLp.toLp 2 (carryMaterialRealFeature t, v t)

theorem carryMaterialRealKernelLift_pairing {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (v : ℝ → H) (t u : ℝ) :
    inner ℝ (carryMaterialRealKernelLift v t) (carryMaterialRealKernelLift v u) =
      carryMaterialRealFeature t*carryMaterialRealFeature u + inner ℝ (v t) (v u) := by
  simp [carryMaterialRealKernelLift, WithLp.prod_inner_apply, mul_comm]

theorem carryMaterialRealOrthogonalResidual_pairing {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (v : ℝ → H) (t u : ℝ)
    (hp : carryMaterialRealFeature 0 ≠ 0)
    (h00 : inner ℝ (v 0) (v 0) = carryMaterialRealFeature 0^2)
    (ht0 : inner ℝ (v t) (v 0) = carryMaterialRealFeature t*carryMaterialRealFeature 0)
    (h0u : inner ℝ (v 0) (v u) = carryMaterialRealFeature 0*carryMaterialRealFeature u) :
    inner ℝ (carryMaterialRealOrthogonalResidual v t) (carryMaterialRealOrthogonalResidual v u) =
      inner ℝ (v t) (v u) - carryMaterialRealFeature t*carryMaterialRealFeature u := by
  simp only [carryMaterialRealOrthogonalResidual, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right, h00, ht0, h0u, conj_trivial]
  field_simp
  ring

theorem carryMaterialRealOrthogonalResidual_center {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (v : ℝ → H) (hp : carryMaterialRealFeature 0 ≠ 0) :
    carryMaterialRealOrthogonalResidual v 0 = 0 := by
  simp [carryMaterialRealOrthogonalResidual, hp]

theorem carryMaterialRealOrthogonalResidual_reconstruct {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (v : ℝ → H) (t : ℝ) :
    v t = (carryMaterialRealFeature t/carryMaterialRealFeature 0) • v 0 +
      carryMaterialRealOrthogonalResidual v t := by
  unfold carryMaterialRealOrthogonalResidual
  abel

/-- The weights removed are the exact zeros in the two material legs,
not a fitted positive factor. -/
def carryMaterialResidualCore (t u : ℝ) : ℝ :=
  (star (carryMaterialResponseAxis t)*carryMaterialResponseAxis u*
    dslope carryMaterialReducedResponse t u).re

def carryMaterialRescaledResidualEnergy {n : ℕ} (c t : Fin n → ℝ) (e : ℝ) : ℝ :=
  ∑ i, ∑ j, c i*c j*(t i*t j)*carryMaterialResidualCore (e*t i) (e*t j)

theorem carryMaterialRealResidual_factor
    (hz : carryMaterialNormalizedResponse 0 = 0) (t u : ℝ) :
    carryMaterialRealResidual t u = t*u*carryMaterialResidualCore t u := by
  have he (s : ℝ) : carryMaterialNormalizedResponse s =
      (s : ℂ)*carryMaterialResponseAxis s := by
    have h := sub_smul_dslope carryMaterialNormalizedResponse 0 s
    simpa only [sub_zero, hz, carryMaterialResponseAxis, Complex.real_smul] using h.symm
  have hc : star (carryMaterialNormalizedResponse t)*carryMaterialNormalizedResponse u*
      dslope carryMaterialReducedResponse t u = ((t*u : ℝ) : ℂ)*
        (star (carryMaterialResponseAxis t)*carryMaterialResponseAxis u*
          dslope carryMaterialReducedResponse t u) := by
    rw [he t, he u]
    simp only [star_mul, Complex.star_def, Complex.conj_ofReal, Complex.ofReal_mul]
    ring
  unfold carryMaterialRealResidual carryMaterialResidualCore
  rw [hc]
  simp

theorem carryMaterialResidual_scaled_energy
    (hz : carryMaterialNormalizedResponse 0 = 0) {n : ℕ} (c t : Fin n → ℝ) (e : ℝ) :
    carryRealKernelEnergy carryMaterialRealResidual c (fun i => e*t i) =
      e^2*carryMaterialRescaledResidualEnergy c t e := by
  unfold carryRealKernelEnergy carryMaterialRescaledResidualEnergy
  simp_rw [carryMaterialRealResidual_factor hz]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem carryMaterialRescaledResidualEnergy_zero {n : ℕ} (c t : Fin n → ℝ) :
    carryMaterialRescaledResidualEnergy c t 0 =
      carryMaterialResidualCore 0 0*(∑ i, c i*t i)^2 := by
  rw [rank_one_energy (fun s : ℝ => s)]
  unfold carryMaterialRescaledResidualEnergy
  simp only [zero_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A fixed pair of rescaled parameters, including coincident directions.
No joint holomorphy of the full material Hilbert state is presumed. -/
theorem carryReal_scaledSlope_continuous (f : ℝ → ℂ)
    (hz : f 0 = 0)
    (hf : DifferentiableAt ℝ f 0)
    (hd : ContinuousAt (deriv f) 0) (a b : ℝ) :
    ContinuousAt (fun e : ℝ => dslope f (e*a) (e*b)) 0 := by
  by_cases hab : b = a
  · subst b
    simp only [dslope_same]
    exact (show ContinuousAt (deriv f) ((0 : ℝ)*a) by
      simpa only [zero_mul] using hd).comp' (f := fun e : ℝ => e*a) (x := 0) (continuousAt_id.mul_const a)
  · let A := dslope f 0
    have hA : ContinuousAt A 0 := continuousAt_dslope_same.mpr hf
    have he (e : ℝ) : dslope f (e*a) (e*b) =
        ((b : ℂ)*A (e*b)-(a : ℂ)*A (e*a))/((b-a : ℝ) : ℂ) := by
      have hn : (b : ℂ)-(a : ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hab
      by_cases he : e = 0
      · subst e
        simp only [zero_mul, dslope_same]
        dsimp only [A]
        rw [dslope_same]
        push_cast
        field_simp [hn]
      · have hsep : e*b ≠ e*a := by
          intro h
          exact hab (mul_left_cancel₀ he h)
        have hfexp (s : ℝ) : f s = (s : ℂ)*A s := by
          have h := sub_smul_dslope f 0 s
          simpa only [sub_zero, hz, Complex.real_smul, A] using h.symm
        rw [dslope_of_ne _ hsep]
        simp only [slope, Complex.real_smul, vsub_eq_sub]
        rw [hfexp (e*b), hfexp (e*a)]
        push_cast
        have hn2 : (e : ℂ)*(b : ℂ)-(e : ℂ)*(a : ℂ) ≠ 0 := by
          exact_mod_cast sub_ne_zero.mpr hsep
        field_simp [hn, hn2, Complex.ofReal_ne_zero.mpr he]
    have hcont : ContinuousAt (fun e : ℝ =>
        ((b : ℂ)*A (e*b)-(a : ℂ)*A (e*a))/((b-a : ℝ) : ℂ)) 0 := by
      have ha : ContinuousAt (fun e : ℝ => A (e*a)) 0 := by
        exact (show ContinuousAt A ((0 : ℝ)*a) by
          simpa only [zero_mul] using hA).comp' (f := fun e : ℝ => e*a) (x := 0) (continuousAt_id.mul_const a)
      have hb : ContinuousAt (fun e : ℝ => A (e*b)) 0 := by
        exact (show ContinuousAt A ((0 : ℝ)*b) by
          simpa only [zero_mul] using hA).comp' (f := fun e : ℝ => e*b) (x := 0) (continuousAt_id.mul_const b)
      exact ((continuousAt_const.mul hb).sub (continuousAt_const.mul ha)).div_const _
    exact hcont.congr (Filter.Eventually.of_forall (fun e => (he e).symm))

theorem carryMaterialReduced_scaledSlope_continuous
    (hz : carryMaterialReducedResponse 0 = 0)
    (hf : DifferentiableAt ℝ carryMaterialReducedResponse 0)
    (hd : ContinuousAt (deriv carryMaterialReducedResponse) 0) (a b : ℝ) :
    ContinuousAt (fun e : ℝ => dslope carryMaterialReducedResponse (e*a) (e*b)) 0 :=
  carryReal_scaledSlope_continuous carryMaterialReducedResponse hz hf hd a b

theorem carryMaterialRescaledResidualEnergy_continuous
    (ha : ContinuousAt carryMaterialResponseAxis 0)
    (hz : carryMaterialReducedResponse 0 = 0)
    (hf : DifferentiableAt ℝ carryMaterialReducedResponse 0)
    (hd : ContinuousAt (deriv carryMaterialReducedResponse) 0)
    {n : ℕ} (c t : Fin n → ℝ) :
    ContinuousAt (carryMaterialRescaledResidualEnergy c t) 0 := by
  have hc (a b : ℝ) : ContinuousAt (fun e : ℝ => carryMaterialResidualCore (e*a) (e*b)) 0 := by
    have hca : ContinuousAt (fun e : ℝ => carryMaterialResponseAxis (e*a)) 0 := by
      exact (show ContinuousAt carryMaterialResponseAxis ((0 : ℝ)*a) by
        simpa only [zero_mul] using ha).comp' (f := fun e : ℝ => e*a) (x := 0) (continuousAt_id.mul_const a)
    have hcb : ContinuousAt (fun e : ℝ => carryMaterialResponseAxis (e*b)) 0 := by
      exact (show ContinuousAt carryMaterialResponseAxis ((0 : ℝ)*b) by
        simpa only [zero_mul] using ha).comp' (f := fun e : ℝ => e*b) (x := 0) (continuousAt_id.mul_const b)
    exact Complex.continuous_re.continuousAt.comp'
      (((Complex.continuous_conj.continuousAt.comp' hca).mul hcb).mul
        (carryMaterialReduced_scaledSlope_continuous hz hf hd a b))
  unfold carryMaterialRescaledResidualEnergy
  apply tendsto_finsetSum
  intro i _
  apply tendsto_finsetSum
  intro j _
  exact continuousAt_const.mul (hc (t i) (t j))

/-- Genuine source sign on every FIXED finite family with nonzero first
material moment, for a family-dependent small scale. It is not a uniform
positive-kernel theorem: the cancelling directions are expressly excluded. -/
theorem carryMaterialResidual_fixed_family_pos
    (hsource : carryMaterialNormalizedResponse 0 = 0)
    (ha : ContinuousAt carryMaterialResponseAxis 0)
    (hz : carryMaterialReducedResponse 0 = 0)
    (hf : DifferentiableAt ℝ carryMaterialReducedResponse 0)
    (hd : ContinuousAt (deriv carryMaterialReducedResponse) 0)
    (hp : 0 < carryMaterialResidualCore 0 0)
    {n : ℕ} (c t : Fin n → ℝ) (hm : (∑ i, c i*t i) ≠ 0) :
    ∀ᶠ e : ℝ in nhds 0, e ≠ 0 →
      0 < carryRealKernelEnergy carryMaterialRealResidual c (fun i => e*t i) := by
  have hc := carryMaterialRescaledResidualEnergy_continuous ha hz hf hd c t
  have he : 0 < carryMaterialRescaledResidualEnergy c t 0 := by
    rw [carryMaterialRescaledResidualEnergy_zero]
    exact mul_pos hp (sq_pos_of_ne_zero hm)
  have hh := (tendsto_order.1 hc).1 0 he
  filter_upwards [hh] with e he hne
  rw [carryMaterialResidual_scaled_energy hsource]
  exact mul_pos (sq_pos_of_ne_zero hne) he

end
end GeometryOfNumbers.Analysis
