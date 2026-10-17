import GeometryOfNumbers.Analysis.CarryMaterialThirdNullSector

/-! Exact all-order cancellation transport of the SAME material residual.
No sign is postulated. The central channel correction and every ordered
cross remain in the finite synthesis. Taylor-shift index is not depth. -/
namespace GeometryOfNumbers.Analysis
open Filter
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- The full retained central correction after k moment cancellations. -/
def carryMaterialNullSynthesis (k : ℕ) {n : ℕ} (c a : Fin n → ℝ) (e : ℝ) : ℂ :=
  ∑ i, (c i : ℂ)*(a i : ℂ)^k*carryMaterialTaylorShift (k+1) (e*a i)

/-- Rescaled original energy, including the central correction. -/
def carryMaterialNullEnergy (k : ℕ) {n : ℕ} (c a : Fin n → ℝ) (e : ℝ) : ℝ :=
  (∑ i, ∑ j, c i*c j*(a i)^k*(a j)^k*
    (dslope (carryMaterialTaylorShift (2*k)) (e*a i) (e*a j)).re) -
      ‖carryMaterialNullSynthesis k c a e‖^2/carryMaterialResponseScale

/-- Central coefficient derived from the same response, with no assigned sign. -/
def carryMaterialNullCoefficient (k : ℕ) : ℝ :=
  (deriv (carryMaterialTaylorShift (2*k)) 0).re -
    ‖carryMaterialTaylorShift (k+1) 0‖^2/carryMaterialResponseScale

theorem carryMaterialTaylorShift_reconstruct (j : ℕ) (t : ℝ) :
    carryMaterialTaylorShift j t = carryMaterialTaylorShift j 0+
      (t : ℂ)*carryMaterialTaylorShift (j+1) t := by
  have h := sub_smul_dslope (carryMaterialTaylorShift j) 0 t
  rw [← carryMaterialTaylorShift_succ] at h
  simp only [sub_zero, Complex.real_smul] at h
  linear_combination -h

/-- Each vanished coefficient sum shifts BOTH arguments of the same
polarized kernel. The full finite double sum is retained at every order. -/
theorem carryMaterial_kernel_power_transport (k : ℕ) (hk : 0 < k)
    {n : ℕ} (c : Fin n → ℂ) (t : Fin n → ℝ)
    (hM : ∀ j, 0 < j → j < k → (∑ i, c i*(t i : ℂ)^j) = 0)
    (hd : ∀ i j, 0 < j → j ≤ k → DifferentiableAt ℝ (carryMaterialTaylorShift (2*j)) (t i)) :
    (∑ i, ∑ l, (c i*(t i : ℂ))*(c l*(t l : ℂ))*
      dslope (carryMaterialTaylorShift 2) (t i) (t l)) =
    ∑ i, ∑ l, (c i*(t i : ℂ)^k)*(c l*(t l : ℂ)^k)*
      dslope (carryMaterialTaylorShift (2*k)) (t i) (t l) := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hz : k = 0
    · subst k
      simp only [zero_add, pow_one, mul_one]
    · have hk' : 0 < k := Nat.pos_of_ne_zero hz
      rw [ih hk' (fun j hj hjk => hM j hj (by omega)) (fun i j hj hjk => hd i j hj (by omega))]
      have hc : (∑ i, c i*(t i : ℂ)^k) = 0 := hM k hk' (by omega)
      have he := carryScalar_finite_energy_shift (carryMaterialTaylorShift (2*k))
        (fun i => c i*(t i : ℂ)^k) t hc (fun i => by
          rw [← carryMaterialTaylorShift_add_two]
          simpa only [Nat.mul_add, Nat.mul_one] using hd i (k+1) (by omega) (by omega))
      rw [← carryMaterialTaylorShift_add_two] at he
      have hn : 2*k+2 = 2*(k+1) := by omega
      rw [hn] at he
      calc
        _ = ∑ i, ∑ l, (c i*(t i : ℂ)^k*(t i : ℂ))*(c l*(t l : ℂ)^k*(t l : ℂ))*
            dslope (carryMaterialTaylorShift (2*(k+1))) (t i) (t l) := he
        _ = _ := by simp only [pow_succ, mul_assoc]

/-- The central rank-one channel is transported, never erased. No parity
or sign is needed for this exact k-th-order identity. -/
theorem carryMaterial_channel_power_transport (k : ℕ) (hk : 0 < k)
    {n : ℕ} (c : Fin n → ℂ) (t : Fin n → ℝ)
    (hM : ∀ j, 0 < j → j < k → (∑ i, c i*(t i : ℂ)^j) = 0) :
    (∑ i, c i*(t i : ℂ)*carryMaterialTaylorShift 2 (t i)) =
      ∑ i, c i*(t i : ℂ)^k*carryMaterialTaylorShift (k+1) (t i) := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hz : k = 0
    · subst k
      simp only [zero_add, pow_one]
    · have hk' : 0 < k := Nat.pos_of_ne_zero hz
      rw [ih hk' (fun j hj hjk => hM j hj (by omega))]
      have hexp (i : Fin n) : c i*(t i : ℂ)^k*carryMaterialTaylorShift (k+1) (t i) =
          c i*(t i : ℂ)^k*carryMaterialTaylorShift (k+1) 0 +
            c i*(t i : ℂ)^(k+1)*carryMaterialTaylorShift (k+1+1) (t i) := by
        rw [carryMaterialTaylorShift_reconstruct (k+1) (t i), pow_succ]
        ring
      simp_rw [hexp, Finset.sum_add_distrib]
      have hc := hM k hk' (by omega)
      have he : (∑ i, c i*(t i : ℂ)^k*carryMaterialTaylorShift (k+1) 0) = 0 := by
        rw [← Finset.sum_mul, hc, zero_mul]
      rw [he, zero_add]

/-- Exact scale normalization of the retained central channel. -/
theorem carryMaterialNullSynthesis_factor (k : ℕ) (hk : 0 < k)
    {n : ℕ} (c a : Fin n → ℝ)
    (hM : ∀ j, 0 < j → j < k → (∑ i, c i*(a i)^j) = 0) (e : ℝ) :
    (∑ i, (c i : ℂ)*((e*a i : ℝ) : ℂ)*carryMaterialTaylorShift 2 (e*a i)) =
      (e : ℂ)^k*carryMaterialNullSynthesis k c a e := by
  have hc (j : ℕ) (hj : 0 < j) (hjk : j < k) :
      (∑ i, (c i : ℂ)*((e*a i : ℝ) : ℂ)^j) = 0 := by
    have hz : (∑ i, (c i : ℂ)*(a i : ℂ)^j) = 0 := by exact_mod_cast hM j hj hjk
    push_cast
    simp only [mul_pow]
    calc
      _ = (e : ℂ)^j*∑ i, (c i : ℂ)*(a i : ℂ)^j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 0 := by rw [hz, mul_zero]
  rw [carryMaterial_channel_power_transport k hk _ _ hc]
  unfold carryMaterialNullSynthesis
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  rw [mul_pow]
  ring


private theorem square_sum {n : ℕ} (v : Fin n → ℂ) :
    (∑ i, v i)^2 = ∑ i, ∑ j, v i*v j := by
  rw [pow_two, Finset.sum_mul]
  simp only [Finset.mul_sum]

/-- Exact transport at EVERY finite order. The central correction is
retained with its original normalization; no sign is assumed anywhere. -/
theorem carryMaterialNull_energy_factor {U : Set ℝ}
    (hs : ∀ t ∈ U, ∀ u ∈ U, (carryMaterialRealResidual t u : ℂ) =
      dslope carryMaterialNormalizedResponse t u-
        carryMaterialTaylorShift 1 t*carryMaterialTaylorShift 1 u /
          (carryMaterialResponseScale : ℂ))
    (hscale : carryMaterialTaylorShift 1 0 = (carryMaterialResponseScale : ℂ))
    (hp : 0 < carryMaterialResponseScale) (k : ℕ) (hk : 0 < k)
    (hreal : ∀ t, conj (carryMaterialTaylorShift (k+1) t) = carryMaterialTaylorShift (k+1) t)
    {n : ℕ} (c a : Fin n → ℝ)
    (hM : ∀ j, 0 < j → j < k → (∑ i, c i*(a i)^j) = 0) (e : ℝ)
    (ht : ∀ i, e*a i ∈ U)
    (hd : ∀ i j, 0 < j → j ≤ k → DifferentiableAt ℝ (carryMaterialTaylorShift (2*j)) (e*a i)) :
    carryRealKernelEnergy carryMaterialRealResidual c (fun i => e*a i) =
      e^(2*k)*carryMaterialNullEnergy k c a e := by
  let t : Fin n → ℝ := fun i => e*a i
  have ha0 : dslope carryMaterialNormalizedResponse 0 0 = (carryMaterialResponseScale : ℂ) := hscale
  have hne : dslope carryMaterialNormalizedResponse 0 0 ≠ 0 := by
    rw [ha0]; exact_mod_cast hp.ne'
  have hpoint (i l : Fin n) : (carryMaterialRealResidual (t i) (t l) : ℂ) =
      ((t i*t l : ℝ) : ℂ)*
        (dslope (carryMaterialTaylorShift 2) (t i) (t l)-
          carryMaterialTaylorShift 2 (t i)*carryMaterialTaylorShift 2 (t l) /
            (carryMaterialResponseScale : ℂ)) := by
    rw [hs _ (ht i) _ (ht l)]
    have h := carryScalar_centered_two_shift carryMaterialNormalizedResponse (t i) (t l)
      hne (hd i 1 (by omega) hk)
    simpa only [ha0, carryMaterialTaylorShift, Function.iterate_succ_apply',
      Function.iterate_zero_apply] using h
  have hMc (j : ℕ) (hj : 0 < j) (hjk : j < k) :
      (∑ i, (c i : ℂ)*(t i : ℂ)^j) = 0 := by
    have hz : (∑ i, (c i : ℂ)*(a i : ℂ)^j) = 0 := by exact_mod_cast hM j hj hjk
    dsimp [t]
    push_cast
    simp only [mul_pow]
    calc
      _ = (e : ℂ)^j*∑ i, (c i : ℂ)*(a i : ℂ)^j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 0 := by rw [hz, mul_zero]
  have hK := carryMaterial_kernel_power_transport k hk (fun i => (c i : ℂ)) t hMc hd
  have hE : (carryRealKernelEnergy carryMaterialRealResidual c t : ℂ) =
      (∑ i, ∑ l, ((c i : ℂ)*(t i : ℂ)^k)*((c l : ℂ)*(t l : ℂ)^k)*
        dslope (carryMaterialTaylorShift (2*k)) (t i) (t l)) -
      (∑ i, (c i : ℂ)*(t i : ℂ)*carryMaterialTaylorShift 2 (t i))^2 /
        (carryMaterialResponseScale : ℂ) := by
    rw [← hK, square_sum, Finset.sum_div]
    simp only [Finset.sum_div]
    rw [← Finset.sum_sub_distrib]
    simp only [← Finset.sum_sub_distrib]
    unfold carryRealKernelEnergy
    push_cast
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro l _
    rw [hpoint]
    push_cast
    ring
  have hepow : (e : ℂ)^(2*k) = (e : ℂ)^k*(e : ℂ)^k := by rw [two_mul, pow_add]
  have hG : (∑ i, ∑ l, ((c i : ℂ)*(t i : ℂ)^k)*((c l : ℂ)*(t l : ℂ)^k)*
      dslope (carryMaterialTaylorShift (2*k)) (t i) (t l)) =
      (e : ℂ)^(2*k)*∑ i, ∑ l, (c i : ℂ)*(c l : ℂ)*(a i : ℂ)^k*(a l : ℂ)^k*
        dslope (carryMaterialTaylorShift (2*k)) (t i) (t l) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    dsimp [t]
    push_cast
    rw [mul_pow, mul_pow, hepow]
    ring
  have hS : conj (carryMaterialNullSynthesis k c a e) = carryMaterialNullSynthesis k c a e := by
    simp only [carryMaterialNullSynthesis, map_sum, map_mul, map_pow, Complex.conj_ofReal, hreal]
  have hN : ((‖carryMaterialNullSynthesis k c a e‖^2 : ℝ) : ℂ) =
      (carryMaterialNullSynthesis k c a e)^2 := by
    rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self, hS, pow_two]
  rw [hG, carryMaterialNullSynthesis_factor k hk c a hM e, mul_pow, ← pow_mul,
    Nat.mul_comm k 2, ← hN] at hE
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul] at hE
  have h := congrArg Complex.re hE
  simp only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.sub_re, zero_mul, sub_zero, Complex.div_ofReal_re, Complex.re_sum] at h
  dsimp [t] at h
  rw [h]
  unfold carryMaterialNullEnergy
  ring

theorem carryMaterialNullEnergy_continuous (k : ℕ)
    (hS : ContinuousAt (carryMaterialTaylorShift (k+1)) 0)
    (hz : carryMaterialTaylorShift (2*k) 0 = 0)
    (hf : DifferentiableAt ℝ (carryMaterialTaylorShift (2*k)) 0)
    (hd : ContinuousAt (deriv (carryMaterialTaylorShift (2*k))) 0)
    {n : ℕ} (c a : Fin n → ℝ) : ContinuousAt (carryMaterialNullEnergy k c a) 0 := by
  have hs : ContinuousAt (carryMaterialNullSynthesis k c a) 0 := by
    unfold carryMaterialNullSynthesis
    apply tendsto_finsetSum
    intro i _
    have ht : ContinuousAt (fun e : ℝ => carryMaterialTaylorShift (k+1) (e*a i)) 0 :=
      (show ContinuousAt (carryMaterialTaylorShift (k+1)) ((0 : ℝ)*a i) by
        simpa only [zero_mul] using hS).comp' (f := fun e : ℝ => e*a i) (x := 0)
          (continuousAt_id.mul_const (a i))
    exact continuousAt_const.mul ht
  have hK : ContinuousAt (fun e : ℝ => ∑ i, ∑ j, c i*c j*(a i)^k*(a j)^k*
      (dslope (carryMaterialTaylorShift (2*k)) (e*a i) (e*a j)).re) 0 := by
    apply tendsto_finsetSum
    intro i _
    apply tendsto_finsetSum
    intro j _
    have h := carryReal_scaledSlope_continuous (carryMaterialTaylorShift (2*k)) hz hf hd (a i) (a j)
    exact continuousAt_const.mul (Complex.continuous_re.continuousAt.comp' h)
  exact hK.sub ((hs.norm.pow 2).div_const _)

theorem carryMaterialNullSynthesis_zero (k : ℕ) {n : ℕ} (c a : Fin n → ℝ) :
    carryMaterialNullSynthesis k c a 0 =
      ((∑ i, c i*(a i)^k : ℝ) : ℂ)*carryMaterialTaylorShift (k+1) 0 := by
  unfold carryMaterialNullSynthesis
  simp only [zero_mul]
  rw [← Finset.sum_mul]
  congr 1
  push_cast
  rfl

/-- The coefficient of the TOTAL energy includes the central square. -/
theorem carryMaterialNullEnergy_zero (k : ℕ) {n : ℕ} (c a : Fin n → ℝ) :
    carryMaterialNullEnergy k c a 0 =
      carryMaterialNullCoefficient k*(∑ i, c i*(a i)^k)^2 := by
  have hG : (∑ i, ∑ j, c i*c j*(a i)^k*(a j)^k*(deriv (carryMaterialTaylorShift (2*k)) 0).re) =
      (deriv (carryMaterialTaylorShift (2*k)) 0).re*(∑ i, c i*(a i)^k)^2 := by
    rw [pow_two, Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  unfold carryMaterialNullEnergy carryMaterialNullCoefficient
  simp only [zero_mul, dslope_same]
  rw [hG, carryMaterialNullSynthesis_zero, norm_mul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]
  ring

end
end GeometryOfNumbers.Analysis
