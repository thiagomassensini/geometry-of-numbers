import GeometryOfNumbers.Analysis.CarryMaterialSecondNullSector
import Mathlib.Analysis.Complex.RealDeriv

/-! Sixth-order control of the SAME material residual. Taylor shifts below
are divided differences of the already synthesized scalar response; they
are not new sources, vertical coordinates, kernels, or Hilbert states. -/
namespace GeometryOfNumbers.Analysis
open Filter
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

/-- Repeated central divided differences of the original material response. -/
def carryMaterialTaylorShift (n : ℕ) : ℝ → ℂ :=
  (fun f : ℝ → ℂ => dslope f 0)^[n] carryMaterialNormalizedResponse

theorem carryMaterialTaylorShift_zero : carryMaterialTaylorShift 0 = carryMaterialNormalizedResponse := rfl

theorem carryMaterialTaylorShift_succ (n : ℕ) :
    carryMaterialTaylorShift (n+1) = dslope (carryMaterialTaylorShift n) 0 := by
  exact Function.iterate_succ_apply' _ _ _

/-- The fourth-power remainder retained in the central channel. -/
def carryMaterialThirdNullSynthesis {n : ℕ} (c a : Fin n → ℝ) (e : ℝ) : ℂ :=
  ∑ i, (c i : ℂ)*(a i : ℂ)^4*carryMaterialTaylorShift 5 (e*a i)

/-- Full sixth-order energy, including the central-channel correction. -/
def carryMaterialThirdNullEnergy {n : ℕ} (c a : Fin n → ℝ) (e : ℝ) : ℝ :=
  (∑ i, ∑ j, c i*c j*(a i)^3*(a j)^3*
    (dslope (carryMaterialTaylorShift 6) (e*a i) (e*a j)).re) -
    e^2/carryMaterialResponseScale*‖carryMaterialThirdNullSynthesis c a e‖^2

private theorem scalar_reconstruct (f : ℝ → ℂ) (t : ℝ) :
    f t = f 0+(t : ℂ)*dslope f 0 t := by
  have h := sub_smul_dslope f 0 t
  simp only [sub_zero, Complex.real_smul] at h
  linear_combination -h

/-- Exact two-step shift of a divided-difference kernel. On a diagonal,
the scalar regularity is explicit; no spectral denominator is divided by. -/
theorem carryScalar_dslope_two_shift (f : ℝ → ℂ) (t u : ℝ)
    (hd : DifferentiableAt ℝ (dslope (dslope f 0) 0) t) :
    dslope f t u = dslope f 0 u+(t : ℂ)*dslope (dslope f 0) 0 t +
      ((t*u : ℝ) : ℂ)*dslope (dslope (dslope f 0) 0) t u := by
  let g := dslope f 0
  let h := dslope g 0
  have hf (x : ℝ) : f x = f 0+(x : ℂ)*g 0+(x : ℂ)^2*h x := by
    rw [scalar_reconstruct f x]
    change f 0+(x : ℂ)*g x = _
    rw [scalar_reconstruct g x]
    ring
  by_cases hne : u = t
  · subst u
    have hr := ((hasDerivAt_const t (f 0)).add
      (((hasDerivAt_id t).ofReal_comp).mul_const (g 0))).add
      ((((hasDerivAt_id t).ofReal_comp).pow 2).mul hd.hasDerivAt)
    have he : (fun x : ℝ => f 0+(x : ℂ)*g 0+(x : ℂ)^2*h x) = f := funext (fun x => (hf x).symm)
    change HasDerivAt (fun x : ℝ => f 0+(x : ℂ)*g 0+(x : ℂ)^2*h x) _ t at hr
    rw [he] at hr
    rw [dslope_same, hr.deriv, dslope_same]
    change _ = g t+(t : ℂ)*h t+((t*t : ℝ) : ℂ)*deriv h t
    rw [scalar_reconstruct g t]
    simp only [zero_add, one_mul, Nat.cast_ofNat, Complex.ofReal_mul,
      Complex.ofReal_one, id_eq, Pi.pow_apply]
    dsimp [g, h] at *
    ring
  · rw [dslope_of_ne f hne, dslope_of_ne (dslope (dslope f 0) 0) hne]
    simp only [slope, Complex.real_smul, vsub_eq_sub, Complex.ofReal_inv]
    have hn : ((u-t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hne
    change ((u-t : ℝ) : ℂ)⁻¹*(f u-f t) =
      g u+(t : ℂ)*h t+((t*u : ℝ) : ℂ)*(((u-t : ℝ) : ℂ)⁻¹*(h u-h t))
    rw [hf u, hf t, scalar_reconstruct g u]
    dsimp [g, h] at *
    push_cast at hn ⊢
    field_simp [hn]
    ring

/-- Center removal followed by a Taylor shift, with its exact rank-one term. -/
theorem carryScalar_centered_two_shift (f : ℝ → ℂ) (t u : ℝ)
    (ha : dslope f 0 0 ≠ 0)
    (hd : DifferentiableAt ℝ (dslope (dslope f 0) 0) t) :
    dslope f t u-dslope f 0 t*dslope f 0 u/dslope f 0 0 =
      ((t*u : ℝ) : ℂ)*
        (dslope (dslope (dslope f 0) 0) t u-
          dslope (dslope f 0) 0 t*dslope (dslope f 0) 0 u/dslope f 0 0) := by
  rw [carryScalar_dslope_two_shift f t u hd,
    scalar_reconstruct (dslope f 0) t, scalar_reconstruct (dslope f 0) u]
  push_cast
  field_simp
  ring

/-- A zero summed coefficient shifts BOTH arguments, preserving all pairs. -/
theorem carryScalar_finite_energy_shift {n : ℕ} (f : ℝ → ℂ)
    (c : Fin n → ℂ) (t : Fin n → ℝ) (hc : ∑ i, c i = 0)
    (hd : ∀ i, DifferentiableAt ℝ (dslope (dslope f 0) 0) (t i)) :
    (∑ i, ∑ j, c i*c j*dslope f (t i) (t j)) =
      ∑ i, ∑ j, (c i*(t i : ℂ))*(c j*(t j : ℂ))*
        dslope (dslope (dslope f 0) 0) (t i) (t j) := by
  simp_rw [carryScalar_dslope_two_shift f _ _ (hd _), mul_add,
    Finset.sum_add_distrib]
  have h1 : (∑ i, ∑ j, c i*c j*dslope f 0 (t j)) = 0 := by
    simp_rw [mul_assoc, ← Finset.mul_sum]
    rw [← Finset.sum_mul, hc, zero_mul]
  have h2 : (∑ i, ∑ j, c i*c j*((t i : ℂ)*dslope (dslope f 0) 0 (t i))) = 0 := by
    have hi (i : Fin n) : (∑ j, c i*c j*((t i : ℂ)*dslope (dslope f 0) 0 (t i))) = 0 := by
      calc
        _ = (c i*(t i : ℂ)*dslope (dslope f 0) 0 (t i)) * ∑ j, c j := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = 0 := by rw [hc, mul_zero]
    simp_rw [hi]
    exact Finset.sum_const_zero
  rw [h1, h2, zero_add, zero_add]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  push_cast
  ring


theorem carryMaterialTaylorShift_add_two (n : ℕ) :
    carryMaterialTaylorShift (n+2) = dslope (dslope (carryMaterialTaylorShift n) 0) 0 := by
  rw [carryMaterialTaylorShift_succ, carryMaterialTaylorShift_succ]

/-- Reality is transported through scalar differences after source synthesis. -/
theorem carryMaterialTaylorShift_conj
    (h0 : ∀ t, conj (carryMaterialNormalizedResponse t) = carryMaterialNormalizedResponse t)
    (n : ℕ) (t : ℝ) : conj (carryMaterialTaylorShift n t) = carryMaterialTaylorShift n t := by
  induction n generalizing t with
  | zero => exact h0 t
  | succ n ih =>
    rw [carryMaterialTaylorShift_succ]
    have he : Complex.conjCLE.toContinuousLinearMap ∘ carryMaterialTaylorShift n =
        carryMaterialTaylorShift n := funext ih
    by_cases ht : (0 : ℝ) = t
    · subst t
      by_cases hd : DifferentiableAt ℝ (carryMaterialTaylorShift n) 0
      · have h := Complex.conjCLE.toContinuousLinearMap.dslope_comp
          (carryMaterialTaylorShift n) 0 0 (fun _ => hd)
        rw [he] at h
        exact h.symm
      · simp only [dslope_same, deriv_zero_of_not_differentiableAt hd, map_zero]
    · have h := Complex.conjCLE.toContinuousLinearMap.dslope_comp
        (carryMaterialTaylorShift n) 0 t (fun heq => False.elim (ht heq))
      rw [he] at h
      exact h.symm

theorem carryMaterialThirdNull_channel_factor
    (h2 : carryMaterialTaylorShift 2 0 = 0) (h4 : carryMaterialTaylorShift 4 0 = 0)
    {n : ℕ} (c a : Fin n → ℝ) (hc : (∑ i, c i*(a i)^2) = 0) (e : ℝ) :
    (∑ i, (c i : ℂ)*((e*a i : ℝ) : ℂ)*carryMaterialTaylorShift 2 (e*a i)) =
      (e : ℂ)^4*carryMaterialThirdNullSynthesis c a e := by
  have hs (t : ℝ) : carryMaterialTaylorShift 2 t =
      (t : ℂ)*carryMaterialTaylorShift 3 0 + (t : ℂ)^3*carryMaterialTaylorShift 5 t := by
    have h := scalar_reconstruct (carryMaterialTaylorShift 2) t
    rw [h2, ← carryMaterialTaylorShift_succ] at h
    have h' := scalar_reconstruct (carryMaterialTaylorShift 3) t
    rw [← carryMaterialTaylorShift_succ] at h'
    have h'' := scalar_reconstruct (carryMaterialTaylorShift 4) t
    rw [h4, ← carryMaterialTaylorShift_succ] at h''
    rw [h, h', h'']
    ring
  have hz : (∑ i, (c i : ℂ)*(a i : ℂ)^2) = 0 := by exact_mod_cast hc
  simp_rw [hs]
  unfold carryMaterialThirdNullSynthesis
  push_cast
  calc
    _ = (e : ℂ)^2*carryMaterialTaylorShift 3 0*(∑ i, (c i : ℂ)*(a i : ℂ)^2) +
        (e : ℂ)^4*∑ i, (c i : ℂ)*(a i : ℂ)^4*carryMaterialTaylorShift 5 (e*a i) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [hz]; ring

private theorem square_sum {n : ℕ} (v : Fin n → ℂ) :
    (∑ i, v i)^2 = ∑ i, ∑ j, v i*v j := by
  rw [pow_two, Finset.sum_mul]
  simp only [Finset.mul_sum]

/-- Two vanishing material moments transport the FULL residual to sixth
order. The retained rank-one correction has order eight, not zero. -/
theorem carryMaterialThirdNull_energy_factor {U : Set ℝ}
    (hs : ∀ t ∈ U, ∀ u ∈ U, (carryMaterialRealResidual t u : ℂ) =
      dslope carryMaterialNormalizedResponse t u-
        carryMaterialTaylorShift 1 t*carryMaterialTaylorShift 1 u /
          (carryMaterialResponseScale : ℂ))
    (hscale : carryMaterialTaylorShift 1 0 = (carryMaterialResponseScale : ℂ))
    (hp : 0 < carryMaterialResponseScale)
    (hz2 : carryMaterialTaylorShift 2 0 = 0) (hz4 : carryMaterialTaylorShift 4 0 = 0)
    (hreal : ∀ t, conj (carryMaterialTaylorShift 5 t) = carryMaterialTaylorShift 5 t)
    {n : ℕ} (c a : Fin n → ℝ)
    (hM1 : (∑ i, c i*a i) = 0) (hM2 : (∑ i, c i*(a i)^2) = 0) (e : ℝ)
    (ht : ∀ i, e*a i ∈ U)
    (hd2 : ∀ i, DifferentiableAt ℝ (carryMaterialTaylorShift 2) (e*a i))
    (hd4 : ∀ i, DifferentiableAt ℝ (carryMaterialTaylorShift 4) (e*a i))
    (hd6 : ∀ i, DifferentiableAt ℝ (carryMaterialTaylorShift 6) (e*a i)) :
    carryRealKernelEnergy carryMaterialRealResidual c (fun i => e*a i) =
      e^6*carryMaterialThirdNullEnergy c a e := by
  let t : Fin n → ℝ := fun i => e*a i
  let d : Fin n → ℂ := fun i => (c i : ℂ)*(t i : ℂ)
  have ha0 : dslope carryMaterialNormalizedResponse 0 0 = (carryMaterialResponseScale : ℂ) := hscale
  have hne : dslope carryMaterialNormalizedResponse 0 0 ≠ 0 := by
    rw [ha0]; exact_mod_cast hp.ne'
  have hpoint (i j : Fin n) : (carryMaterialRealResidual (t i) (t j) : ℂ) =
      ((t i*t j : ℝ) : ℂ)*
        (dslope (carryMaterialTaylorShift 2) (t i) (t j)-
          carryMaterialTaylorShift 2 (t i)*carryMaterialTaylorShift 2 (t j) /
            (carryMaterialResponseScale : ℂ)) := by
    rw [hs _ (ht i) _ (ht j)]
    have h := carryScalar_centered_two_shift carryMaterialNormalizedResponse (t i) (t j) hne (hd2 i)
    simpa only [ha0, carryMaterialTaylorShift, Function.iterate_succ_apply',
      Function.iterate_zero_apply] using h
  have hd : (∑ i, d i) = 0 := by
    dsimp [d, t]
    push_cast
    have hz : (∑ i, (c i : ℂ)*(a i : ℂ)) = 0 := by exact_mod_cast hM1
    calc
      _ = (e : ℂ)*∑ i, (c i : ℂ)*(a i : ℂ) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
      _ = 0 := by rw [hz, mul_zero]
  have hdd : (∑ i, d i*(t i : ℂ)) = 0 := by
    dsimp [d, t]
    push_cast
    have hz : (∑ i, (c i : ℂ)*(a i : ℂ)^2) = 0 := by exact_mod_cast hM2
    calc
      _ = (e : ℂ)^2*∑ i, (c i : ℂ)*(a i : ℂ)^2 := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
      _ = 0 := by rw [hz, mul_zero]
  have hfirst := carryScalar_finite_energy_shift (carryMaterialTaylorShift 2) d t hd hd4
  rw [← carryMaterialTaylorShift_add_two 2] at hfirst
  have hsecond := carryScalar_finite_energy_shift (carryMaterialTaylorShift 4)
    (fun i => d i*(t i : ℂ)) t hdd hd6
  rw [← carryMaterialTaylorShift_add_two 4] at hsecond
  have hE : (carryRealKernelEnergy carryMaterialRealResidual c t : ℂ) =
      (∑ i, ∑ j, (d i*(t i : ℂ)^2)*(d j*(t j : ℂ)^2)*
        dslope (carryMaterialTaylorShift 6) (t i) (t j)) -
      (∑ i, d i*carryMaterialTaylorShift 2 (t i))^2/(carryMaterialResponseScale : ℂ) := by
    have hk : (∑ i, ∑ j, d i*d j*dslope (carryMaterialTaylorShift 2) (t i) (t j)) =
        ∑ i, ∑ j, (d i*(t i : ℂ)^2)*(d j*(t j : ℂ)^2)*
          dslope (carryMaterialTaylorShift 6) (t i) (t j) := by
      rw [hfirst, hsecond]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      ring
    rw [← hk, square_sum, Finset.sum_div]
    simp only [Finset.sum_div]
    rw [← Finset.sum_sub_distrib]
    simp only [← Finset.sum_sub_distrib]
    unfold carryRealKernelEnergy
    push_cast
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [hpoint]
    dsimp [d]
    push_cast
    ring
  have hG : (∑ i, ∑ j, (d i*(t i : ℂ)^2)*(d j*(t j : ℂ)^2)*
      dslope (carryMaterialTaylorShift 6) (t i) (t j)) =
      (e : ℂ)^6*∑ i, ∑ j, (c i : ℂ)*(c j : ℂ)*(a i : ℂ)^3*(a j : ℂ)^3*
        dslope (carryMaterialTaylorShift 6) (t i) (t j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    dsimp [d, t]
    push_cast
    ring
  have hS : conj (carryMaterialThirdNullSynthesis c a e) = carryMaterialThirdNullSynthesis c a e := by
    simp only [carryMaterialThirdNullSynthesis, map_sum, map_mul, map_pow, Complex.conj_ofReal, hreal]
  have hN : ((‖carryMaterialThirdNullSynthesis c a e‖^2 : ℝ) : ℂ) =
      (carryMaterialThirdNullSynthesis c a e)^2 := by
    rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self, hS, pow_two]
  rw [hG, carryMaterialThirdNull_channel_factor hz2 hz4 c a hM2 e, mul_pow] at hE
  rw [← hN] at hE
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul] at hE
  have h := congrArg Complex.re hE
  simp only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.sub_re, zero_mul, sub_zero, Complex.div_ofReal_re,
    Complex.re_sum] at h
  unfold carryMaterialThirdNullEnergy
  dsimp [t] at h ⊢
  calc
    _ = e^6*(∑ i, ∑ j, c i*c j*(a i)^3*(a j)^3*
        (dslope (carryMaterialTaylorShift 6) (e*a i) (e*a j)).re) -
        e^8*‖carryMaterialThirdNullSynthesis c a e‖^2/carryMaterialResponseScale := by
      simpa only [← pow_mul] using h
    _ = _ := by ring


theorem carryMaterialThirdNullEnergy_continuous
    (h5 : ContinuousAt (carryMaterialTaylorShift 5) 0)
    (hz : carryMaterialTaylorShift 6 0 = 0)
    (h6 : DifferentiableAt ℝ (carryMaterialTaylorShift 6) 0)
    (hd6 : ContinuousAt (deriv (carryMaterialTaylorShift 6)) 0)
    {n : ℕ} (c a : Fin n → ℝ) : ContinuousAt (carryMaterialThirdNullEnergy c a) 0 := by
  have hS : ContinuousAt (carryMaterialThirdNullSynthesis c a) 0 := by
    unfold carryMaterialThirdNullSynthesis
    apply tendsto_finsetSum
    intro i _
    have ht : ContinuousAt (fun e : ℝ => carryMaterialTaylorShift 5 (e*a i)) 0 :=
      (show ContinuousAt (carryMaterialTaylorShift 5) ((0 : ℝ)*a i) by
        simpa only [zero_mul] using h5).comp' (f := fun e : ℝ => e*a i) (x := 0) (continuousAt_id.mul_const (a i))
    exact continuousAt_const.mul ht
  have hK : ContinuousAt (fun e : ℝ => ∑ i, ∑ j, c i*c j*(a i)^3*(a j)^3*
      (dslope (carryMaterialTaylorShift 6) (e*a i) (e*a j)).re) 0 := by
    apply tendsto_finsetSum
    intro i _
    apply tendsto_finsetSum
    intro j _
    have hh := carryReal_scaledSlope_continuous (carryMaterialTaylorShift 6) hz h6 hd6 (a i) (a j)
    exact continuousAt_const.mul (Complex.continuous_re.continuousAt.comp' hh)
  exact hK.sub (((continuousAt_id.pow 2).div_const _).mul (hS.norm.pow 2))

/-- All ordered pairs give the square of the third material moment at zero. -/
theorem carryMaterialThirdNullEnergy_zero {n : ℕ} (c a : Fin n → ℝ) :
    carryMaterialThirdNullEnergy c a 0 =
      (deriv (carryMaterialTaylorShift 6) 0).re*(∑ i, c i*(a i)^3)^2 := by
  unfold carryMaterialThirdNullEnergy
  simp only [zero_mul, dslope_same, zero_pow (by decide : 2 ≠ 0), zero_div, sub_zero]
  rw [pow_two, Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end
end GeometryOfNumbers.Analysis
