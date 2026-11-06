import SigmaZeroObstruction
import SourceBezout

/-!
# The original displaced sigma source and its Bezout recurrence

The source coefficients are the even Taylor coefficients of the original displaced product
`completedSigmaDensity d t = F(t-id) F(t+id)`.  The moment sequence remains the original
`completedSigmaLogJet`, with the factor two forced by the logarithmic derivative equation.
-/

namespace CarrySigmaObstruction

open CarrySigmaSource CarrySourceBezout Filter Topology
open scoped BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- Normalized Taylor coefficient at the origin. -/
def sigmaTaylorCoefficient (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  iteratedDeriv n f 0 / (n.factorial : ℝ)

/-- The descended source coefficients of the original displaced product `D_d(t)=C_d(t²)`. -/
def completedSigmaDisplacedSourceCoefficient (d : ℝ) (n : ℕ) : ℝ :=
  sigmaTaylorCoefficient (completedSigmaDensity d) (2 * n)

/-- The Taylor series in `u=t²` obtained from the even coefficients of the original density. -/
def completedSigmaDisplacedSourceTaylorSeries (d : ℝ) :
    FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ (completedSigmaDisplacedSourceCoefficient d)

/-- The even-variable source series of the original displaced product. -/
def completedSigmaDisplacedSourceSeries (d : ℝ) : PowerSeries ℝ :=
  PowerSeries.mk (completedSigmaDisplacedSourceCoefficient d)

/-- The moments in the source recurrence are twice the original sigma logarithmic jets. -/
def completedSigmaDisplacedMoment (d : ℝ) (n : ℕ) : ℝ :=
  2 * completedSigmaLogJet d n

/-- Taylor coefficients multiply by finite Cauchy convolution. -/
private theorem sigmaTaylorCoefficient_mul {f g : ℝ → ℝ}
    (hf : AnalyticAt ℝ f 0) (hg : AnalyticAt ℝ g 0) (n : ℕ) :
    sigmaTaylorCoefficient (fun t => f t * g t) n =
      ∑ j ∈ Finset.range (n + 1),
        sigmaTaylorCoefficient f j * sigmaTaylorCoefficient g (n - j) := by
  change iteratedDeriv n (f * g) 0 / (n.factorial : ℝ) =
    ∑ j ∈ Finset.range (n + 1),
      (iteratedDeriv j f 0 / (j.factorial : ℝ)) *
        (iteratedDeriv (n - j) g 0 / ((n - j).factorial : ℝ))
  rw [iteratedDeriv_mul hf.contDiffAt hg.contDiffAt, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Nat.cast_choose ℝ (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hj0 : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hnj : ((n - j).factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n - j)
  field_simp

/-- Differentiation shifts normalized Taylor coefficients with its exact integer factor. -/
private theorem sigmaTaylorCoefficient_deriv {f : ℝ → ℝ} (n : ℕ) :
    sigmaTaylorCoefficient (deriv f) n =
      (n + 1 : ℝ) * sigmaTaylorCoefficient f (n + 1) := by
  unfold sigmaTaylorCoefficient
  rw [← iteratedDeriv_succ', Nat.factorial_succ]
  push_cast
  field_simp [Nat.factorial_ne_zero]

/-- Split a finite initial interval into its even and odd indices. -/
private theorem sigma_sum_range_even_odd {α : Type*} [AddCommMonoid α]
    (f : ℕ → α) (n : ℕ) :
    (∑ i ∈ Finset.range (2 * n + 2), f i) =
      ∑ j ∈ Finset.range (n + 1), (f (2 * j) + f (2 * j + 1)) := by
  induction n with
  | zero =>
      simp only [Nat.mul_zero, Nat.zero_add]
      rw [show 2 = 1 + 1 by rfl, Finset.sum_range_succ,
        show 1 = 0 + 1 by rfl, Finset.sum_range_succ]
      simp
  | succ n ih =>
      calc
        (∑ i ∈ Finset.range (2 * (n + 1) + 2), f i) =
            (∑ i ∈ Finset.range (2 * n + 2), f i) + f (2 * n + 2) + f (2 * n + 3) := by
              rw [show 2 * (n + 1) + 2 = (2 * n + 3) + 1 by omega,
                Finset.sum_range_succ,
                show 2 * n + 3 = (2 * n + 2) + 1 by omega,
                Finset.sum_range_succ]
        _ = (∑ j ∈ Finset.range (n + 1), (f (2 * j) + f (2 * j + 1))) +
              f (2 * n + 2) + f (2 * n + 3) := by rw [ih]
        _ = ∑ j ∈ Finset.range (n + 1 + 1), (f (2 * j) + f (2 * j + 1)) := by
              have hR :
                  (∑ j ∈ Finset.range (n + 2), (f (2 * j) + f (2 * j + 1))) =
                    (∑ j ∈ Finset.range (n + 1), (f (2 * j) + f (2 * j + 1))) +
                      (f (2 * (n + 1)) + f (2 * (n + 1) + 1)) := by
                rw [show n + 2 = (n + 1) + 1 by omega, Finset.sum_range_succ]
              rw [show n + 1 + 1 = n + 2 by omega, hR,
                show 2 * n + 2 = 2 * (n + 1) by omega,
                show 2 * n + 3 = 2 * (n + 1) + 1 by omega]
              ac_rfl

/-- The original density is analytic at the center, as the real restriction of the displaced
product. -/
private theorem completedSigmaDensity_analyticAt_origin (d : ℝ)
    (hd₁ : -(1 / 2 : ℝ) < d) (hd₂ : d < (1 / 2 : ℝ)) :
    AnalyticAt ℝ (completedSigmaDensity d) 0 := by
  have hD := displacedProductC_analyticAt_origin d hd₁ hd₂
  have hreal : AnalyticAt ℝ
      (fun t : ℝ => (displacedProductC d (t : ℂ)).re) 0 := hD.re_ofReal
  have heq : (completedSigmaDensity d) =
      (fun t : ℝ => (displacedProductC d (t : ℂ)).re) := by
    funext t
    rw [displacedProductC_ofReal_eq_density d t hd₁ hd₂, Complex.ofReal_re]
  rw [heq]
  exact hreal

/-- Every odd Taylor coefficient of the original real density vanishes by its exact evenness. -/
private theorem completedSigmaDensity_iteratedDeriv_odd_eq_zero (d : ℝ) (n : ℕ)
    (hd₁ : -(1 / 2 : ℝ) < d) (hd₂ : d < (1 / 2 : ℝ)) :
    iteratedDeriv (2 * n + 1) (completedSigmaDensity d) 0 = 0 := by
  have heven : (fun t : ℝ => completedSigmaDensity d (-t)) =
      (completedSigmaDensity d) := by
    funext t
    exact completedSigmaDensity_even d t hd₁ hd₂
  have hderiv := congrArg
    (fun f : ℝ → ℝ => iteratedDeriv (2 * n + 1) f 0) heven
  rw [iteratedDeriv_comp_neg] at hderiv
  have hpowEven (k : ℕ) : (-1 : ℝ) ^ (k * 2) = 1 := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Nat.succ_mul, pow_add, ih]
        norm_num
  have hpow : (-1 : ℝ) ^ (2 * n + 1) = -1 := by
    rw [show 2 * n + 1 = n * 2 + 1 by omega, pow_add, hpowEven]
    norm_num
  simp only [neg_zero, hpow, smul_eq_mul] at hderiv
  linarith

/-- The even Taylor series of the original density converges to the density at `t²` near zero.
This proves the real-axis descent `D_d(t)=C_d(t²)` using the untouched displaced product. -/
theorem completedSigmaDisplacedSourceTaylorSeries_sums_to_density (d : ℝ)
    (hd₁ : -(1 / 2 : ℝ) < d) (hd₂ : d < (1 / 2 : ℝ)) :
    ∀ᶠ t : ℝ in 𝓝 0,
      (completedSigmaDisplacedSourceTaylorSeries d).sum (t ^ 2) =
        completedSigmaDensity d t := by
  let ρ : ℝ → ℝ := completedSigmaDensity d
  let a : ℕ → ℝ := fun n => sigmaTaylorCoefficient ρ n
  let T : FormalMultilinearSeries ℝ ℝ ℝ := FormalMultilinearSeries.ofScalars ℝ a
  let Q := completedSigmaDisplacedSourceTaylorSeries d
  have hρ : AnalyticAt ℝ ρ 0 := completedSigmaDensity_analyticAt_origin d hd₁ hd₂
  have hT : HasFPowerSeriesAt ρ T 0 := by
    exact hρ.hasFPowerSeriesAt
  have hTpos : 0 < T.radius := hT.radius_pos
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 hTpos with ⟨rNN, hrNN, hradius⟩
  obtain ⟨C, hC, hTbound⟩ := T.norm_mul_pow_le_of_lt_radius hradius
  have hrNNReal : (0 : NNReal) < rNN := by exact_mod_cast hrNN
  let rSq : NNReal := rNN * rNN
  have hQbound : ∀ n, ‖Q n‖ * (rSq : ℝ) ^ n ≤ C := by
    intro n
    have hcoeff : ‖Q n‖ = ‖T (2 * n)‖ := by
      simp [Q, T, a, ρ, completedSigmaDisplacedSourceTaylorSeries,
        completedSigmaDisplacedSourceCoefficient, sigmaTaylorCoefficient]
    have hpow : (rSq : ℝ) ^ n = (rNN : ℝ) ^ (2 * n) := by
      calc
        (rSq : ℝ) ^ n = ((rNN : ℝ) * (rNN : ℝ)) ^ n := by
          simp only [rSq, NNReal.coe_mul]
        _ = ((rNN : ℝ) ^ 2) ^ n := by rw [pow_two]
        _ = (rNN : ℝ) ^ (2 * n) := by rw [← pow_mul]
    rw [hcoeff, hpow]
    exact hTbound (2 * n)
  have hQradius : 0 < Q.radius := by
    have hrSq : (0 : NNReal) < rSq := mul_pos hrNNReal hrNNReal
    have hle := Q.le_radius_of_bound C hQbound
    exact lt_of_lt_of_le (by exact_mod_cast hrSq) hle
  have hTsum : ∀ᶠ t : ℝ in 𝓝 0,
      HasSum (fun n => a n * t ^ n) (ρ t) := by
    filter_upwards [hT.eventually_hasSum] with t ht
    simpa [T, a, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm] using ht
  have hQseries : HasFPowerSeriesAt Q.sum Q 0 :=
    (Q.hasFPowerSeriesOnBall hQradius).hasFPowerSeriesAt
  have hQsum : ∀ᶠ u : ℝ in 𝓝 0,
      HasSum (fun n => Q n (fun _ : Fin n => u)) (Q.sum u) := by
    simpa only [zero_add] using hQseries.eventually_hasSum
  have hsq : Filter.Tendsto (fun t : ℝ => t ^ 2) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => t ^ 2) := by fun_prop
    simpa using (hc.continuousAt : ContinuousAt (fun t : ℝ => t ^ 2) 0).tendsto
  have hQsumSq : ∀ᶠ t : ℝ in 𝓝 0,
      HasSum (fun n => a (2 * n) * t ^ (2 * n)) (Q.sum (t ^ 2)) := by
    filter_upwards [hsq.eventually hQsum] with t ht
    have ht' : HasSum (fun n => Q n (fun _ : Fin n => t ^ 2)) (Q.sum (t ^ 2)) := by
      simpa only [zero_add] using ht
    convert ht' using 1
    · funext n
      symm
      simp only [Q, completedSigmaDisplacedSourceTaylorSeries,
        completedSigmaDisplacedSourceCoefficient, a,
        FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
      rw [pow_mul]
  have hoddSum (t : ℝ) :
      HasSum (fun n => a (2 * n + 1) * t ^ (2 * n + 1)) 0 := by
    have hterm : ∀ n, a (2 * n + 1) * t ^ (2 * n + 1) = 0 := by
      intro n
      have hcoeff : a (2 * n + 1) = 0 := by
        change sigmaTaylorCoefficient ρ (2 * n + 1) = 0
        unfold sigmaTaylorCoefficient
        change iteratedDeriv (2 * n + 1) (completedSigmaDensity d) 0 /
            ((2 * n + 1).factorial : ℝ) = 0
        rw [completedSigmaDensity_iteratedDeriv_odd_eq_zero d n hd₁ hd₂]
        simp
      rw [hcoeff]
      simp
    simp [hterm]
  filter_upwards [hTsum, hQsumSq] with t hTaylorAtT hEvenAtT
  let b : ℕ → ℝ := fun n => a n * t ^ n
  have hevenSum : HasSum (fun n => b (2 * n)) (Q.sum (t ^ 2)) := by
    simpa [b] using hEvenAtT
  have hoddSum' : HasSum (fun n => b (2 * n + 1)) 0 := by
    simpa [b] using hoddSum t
  have hfull := HasSum.even_add_odd (f := b) hevenSum hoddSum'
  have hfull' : HasSum (fun n => a n * t ^ n) (Q.sum (t ^ 2)) := by
    simpa [b] using hfull
  exact hfull'.unique hTaylorAtT

/-- The original complex displaced product has this descended source on the real axis. -/
theorem displacedProductC_eq_completedSigmaDisplacedSource_eventually (d : ℝ)
    (hd₁ : -(1 / 2 : ℝ) < d) (hd₂ : d < (1 / 2 : ℝ)) :
    ∀ᶠ t : ℝ in 𝓝 0,
      displacedProductC d (t : ℂ) =
        ((completedSigmaDisplacedSourceTaylorSeries d).sum (t ^ 2) : ℂ) := by
  filter_upwards [completedSigmaDisplacedSourceTaylorSeries_sums_to_density d hd₁ hd₂]
    with t ht
  calc
    displacedProductC d (t : ℂ) = (completedSigmaDensity d t : ℂ) :=
      displacedProductC_ofReal_eq_density d t hd₁ hd₂
    _ = ((completedSigmaDisplacedSourceTaylorSeries d).sum (t ^ 2) : ℂ) := by
      rw [← ht]

/-- Near the center, differentiating `log D_d` gives `D'_d = (log D_d)' D_d`. -/
private theorem completedSigmaDensity_deriv_eq_logDeriv_mul_eventually (d : ℝ)
    (hd₁ : -(1 / 2 : ℝ) < d) (hd₂ : d < (1 / 2 : ℝ)) :
    ∀ᶠ t : ℝ in 𝓝 0,
      deriv (completedSigmaDensity d) t =
        deriv (fun x : ℝ => Real.log (completedSigmaDensity d x)) t *
          completedSigmaDensity d t := by
  have hρ := completedSigmaDensity_analyticAt_origin d hd₁ hd₂
  have hzero : completedSigmaDensity d 0 ≠ 0 :=
    (completedSigmaDensity_zero_pos d hd₁ hd₂).ne'
  have hnonzero : ∀ᶠ t : ℝ in 𝓝 0, completedSigmaDensity d t ≠ 0 :=
    hρ.continuousAt.eventually_ne hzero
  filter_upwards [hρ.eventually_analyticAt, hnonzero] with t hρt hnt
  have hlogDeriv := (hρt.differentiableAt.hasDerivAt.log hnt).deriv
  have hmul := congrArg (fun x : ℝ => x * completedSigmaDensity d t) hlogDeriv
  rw [div_mul_cancel₀ _ hnt] at hmul
  exact hmul.symm

/-- The exact coefficient recurrence follows from the logarithmic derivative of the original
density.  Odd/even parity leaves precisely the finite convolution by the original jets. -/
theorem completedSigmaDisplacedSource_coefficient_recurrence (d : ℝ)
    (hd₁ : -(1 / 2 : ℝ) < d) (hd₂ : d < (1 / 2 : ℝ)) (n : ℕ) :
    (2 * n + 2 : ℝ) * completedSigmaDisplacedSourceCoefficient d (n + 1) =
      -4 * ∑ j ∈ Finset.range (n + 1),
        completedSigmaLogJet d j * completedSigmaDisplacedSourceCoefficient d (n - j) := by
  let L : ℝ → ℝ := fun t => Real.log (completedSigmaDensity d t)
  let f : ℝ → ℝ := fun t => deriv L t
  let ρ : ℝ → ℝ := completedSigmaDensity d
  have hL : AnalyticAt ℝ L 0 := completedSigmaLogDensity_analyticAt_origin d hd₁ hd₂
  have hf : AnalyticAt ℝ f 0 := hL.deriv
  have hρ : AnalyticAt ℝ ρ 0 := completedSigmaDensity_analyticAt_origin d hd₁ hd₂
  have hlocal := completedSigmaDensity_deriv_eq_logDeriv_mul_eventually d hd₁ hd₂
  have hlocalEq : (fun t : ℝ => deriv ρ t) =ᶠ[𝓝 0]
      (fun t : ℝ => f t * ρ t) := by
    filter_upwards [hlocal] with t ht
    simpa [f, ρ, L] using ht
  have hiter := hlocalEq.iteratedDeriv_eq (2 * n + 1)
  have hcoeffEq : sigmaTaylorCoefficient (deriv ρ) (2 * n + 1) =
      sigmaTaylorCoefficient (fun t => f t * ρ t) (2 * n + 1) := by
    unfold sigmaTaylorCoefficient f ρ L at *
    rw [hiter]
  have hleft := sigmaTaylorCoefficient_deriv (f := ρ) (2 * n + 1)
  have hright := sigmaTaylorCoefficient_mul hf hρ (2 * n + 1)
  have hprod : sigmaTaylorCoefficient (fun t => f t * ρ t) (2 * n + 1) =
      -4 * ∑ j ∈ Finset.range (n + 1),
        completedSigmaLogJet d j * completedSigmaDisplacedSourceCoefficient d (n - j) := by
    let F : ℕ → ℝ := fun i =>
      sigmaTaylorCoefficient f i * sigmaTaylorCoefficient ρ (2 * n + 1 - i)
    have hevenL (j : ℕ) : sigmaTaylorCoefficient f (2 * j) = 0 := by
      change completedSigmaLogDensityDerivativeTaylorCoefficient d (2 * j) = 0
      exact completedSigmaLogDensityDerivativeTaylorCoefficient_even_eq_zero d j hd₁ hd₂
    have hevenF (j : ℕ) : F (2 * j) = 0 := by
      change sigmaTaylorCoefficient f (2 * j) *
        sigmaTaylorCoefficient ρ (2 * n + 1 - 2 * j) = 0
      rw [hevenL]
      simp
    calc
      _ = ∑ i ∈ Finset.range (2 * n + 2), F i := by simpa [F] using hright
      _ = ∑ j ∈ Finset.range (n + 1), (F (2 * j) + F (2 * j + 1)) :=
        sigma_sum_range_even_odd F n
      _ = -4 * ∑ j ∈ Finset.range (n + 1),
            completedSigmaLogJet d j * completedSigmaDisplacedSourceCoefficient d (n - j) := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const_zero, hevenF, zero_add]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        have hsub : 2 * n + 1 - (2 * j + 1) = 2 * (n - j) := by omega
        have hodd : sigmaTaylorCoefficient f (2 * j + 1) =
            -4 * completedSigmaLogJet d j := by
          dsimp [f, L, sigmaTaylorCoefficient]
          simpa [completedSigmaLogDensityDerivativeTaylorCoefficient] using
            completedSigmaLogDensityDerivativeTaylorCoefficient_odd_eq_jet d j
        change sigmaTaylorCoefficient f (2 * j + 1) *
          sigmaTaylorCoefficient ρ (2 * n + 1 - (2 * j + 1)) = _
        rw [hodd, hsub]
        simp only [ρ, completedSigmaDisplacedSourceCoefficient]
        ring
  have hidx : 2 * n + 1 + 1 = 2 * (n + 1) := by omega
  have hρidx : sigmaTaylorCoefficient ρ (2 * n + 1 + 1) =
      completedSigmaDisplacedSourceCoefficient d (n + 1) := by
    rw [hidx]
    simp [ρ, completedSigmaDisplacedSourceCoefficient]
  have hleft' : sigmaTaylorCoefficient (deriv ρ) (2 * n + 1) =
      (2 * n + 2 : ℝ) * completedSigmaDisplacedSourceCoefficient d (n + 1) := by
    calc
      _ = ((2 * n + 1 + 1 : ℕ) : ℝ) *
          sigmaTaylorCoefficient ρ (2 * n + 1 + 1) := by simpa using hleft
      _ = _ := by rw [hρidx]; push_cast; ring
  calc
    (2 * n + 2 : ℝ) * completedSigmaDisplacedSourceCoefficient d (n + 1) =
        sigmaTaylorCoefficient (deriv ρ) (2 * n + 1) := hleft'.symm
    _ = sigmaTaylorCoefficient (fun t => f t * ρ t) (2 * n + 1) := hcoeffEq
    _ = -4 * ∑ j ∈ Finset.range (n + 1),
          completedSigmaLogJet d j * completedSigmaDisplacedSourceCoefficient d (n - j) := hprod

/-- The even-variable source satisfies the generic Bézout source recurrence with moments
`2 * completedSigmaLogJet`. -/
theorem completedSigmaDisplacedSource_recurrence (d : ℝ)
    (hd₁ : -(1 / 2 : ℝ) < d) (hd₂ : d < (1 / 2 : ℝ)) :
    SourceRecurrence (completedSigmaDisplacedSourceCoefficient d)
      (completedSigmaDisplacedMoment d) := by
  apply PowerSeries.ext
  intro n
  change PowerSeries.coeff n
      (sourceSeries (completedSigmaDisplacedSourceCoefficient d) *
        momentSeries (completedSigmaDisplacedMoment d)) =
    PowerSeries.coeff n
      (-(PowerSeries.derivative ℝ
        (sourceSeries (completedSigmaDisplacedSourceCoefficient d))))
  rw [PowerSeries.coeff_mul, ← Finset.Nat.sum_antidiagonal_swap,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [sourceSeries, momentSeries, PowerSeries.coeff_mk, map_neg,
    PowerSeries.coeff_derivative]
  have hrec := completedSigmaDisplacedSource_coefficient_recurrence d hd₁ hd₂ n
  have hsum :
      (∑ j ∈ Finset.range (n + 1),
        (2 * completedSigmaLogJet d j) *
          completedSigmaDisplacedSourceCoefficient d (n - j)) =
        -((n + 1 : ℝ) * completedSigmaDisplacedSourceCoefficient d (n + 1)) := by
    calc
      _ = 2 * ∑ j ∈ Finset.range (n + 1),
          completedSigmaLogJet d j *
            completedSigmaDisplacedSourceCoefficient d (n - j) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j hj
              ring
      _ = _ := by nlinarith [hrec]
  simpa [completedSigmaDisplacedMoment, mul_comm] using hsum

/-- The power-series form of the displaced-source recurrence. -/
theorem completedSigmaDisplacedSourceSeries_mul_moments_eq_neg_derivative (d : ℝ)
    (hd₁ : -(1 / 2 : ℝ) < d) (hd₂ : d < (1 / 2 : ℝ)) :
    completedSigmaDisplacedSourceSeries d *
        momentSeries (completedSigmaDisplacedMoment d) =
      -(PowerSeries.derivative ℝ (completedSigmaDisplacedSourceSeries d)) := by
  simpa [SourceRecurrence, completedSigmaDisplacedSourceSeries, sourceSeries] using
    (completedSigmaDisplacedSource_recurrence d hd₁ hd₂)

/-- Since the original source has positive constant term, its formal reciprocal exists; division
of the source derivative by the source recovers exactly twice the original sigma jets. -/
theorem completedSigmaDisplacedSource_log_derivative_eq_moments (d : ℝ)
    (hd₁ : -(1 / 2 : ℝ) < d) (hd₂ : d < (1 / 2 : ℝ)) :
    -(PowerSeries.derivative ℝ (completedSigmaDisplacedSourceSeries d)) *
        (completedSigmaDisplacedSourceSeries d)⁻¹ =
      momentSeries (completedSigmaDisplacedMoment d) := by
  let C := completedSigmaDisplacedSourceSeries d
  let H := momentSeries (completedSigmaDisplacedMoment d)
  have hC0 : PowerSeries.constantCoeff C ≠ 0 := by
    have hpos : 0 < completedSigmaDisplacedSourceCoefficient d 0 := by
      simpa [completedSigmaDisplacedSourceCoefficient, sigmaTaylorCoefficient] using
        completedSigmaDensity_zero_pos d hd₁ hd₂
    simpa [C, completedSigmaDisplacedSourceSeries, PowerSeries.constantCoeff_mk] using
      hpos.ne'
  have hrec := completedSigmaDisplacedSourceSeries_mul_moments_eq_neg_derivative
    d hd₁ hd₂
  have hrec' : C * H = -(PowerSeries.derivative ℝ C) := hrec
  have hmul' : H = C⁻¹ * -(PowerSeries.derivative ℝ C) := by
    calc
      H = (C⁻¹ * C) * H := by simp [PowerSeries.inv_mul_cancel C hC0]
      _ = C⁻¹ * (C * H) := by simp [mul_assoc]
      _ = C⁻¹ * -(PowerSeries.derivative ℝ C) := by rw [hrec']
  calc
    -(PowerSeries.derivative ℝ C) * C⁻¹ =
        C⁻¹ * -(PowerSeries.derivative ℝ C) := by ring
    _ = H := hmul'.symm

/-- The exact scale-two Hankel matrix is the original sigma matrix multiplied by a positive
scalar.  This keeps the original `completedSigmaLogJet` as the matrix moment sequence. -/
theorem completedSigmaDisplacedMoment_hankel_eq_two_sigmaMatrix (d : ℝ)
    (s r : ℕ) :
    hankelMatrix (completedSigmaDisplacedMoment d) s r =
      (2 : ℝ) • CarryMovingSigma.sigmaMatrix d s r := by
  ext i j
  simp [hankelMatrix, completedSigmaDisplacedMoment,
    CarryMovingSigma.sigmaMatrix, CarrySelfAdjointOperator.sourceMomentMatrix]

/-- The source convolution has nonzero constant term because the original displaced density is
strictly positive at its center. -/
theorem completedSigmaDisplacedSourceCoefficient_zero_pos (d : ℝ)
    (hd₁ : -(1 / 2 : ℝ) < d) (hd₂ : d < (1 / 2 : ℝ)) :
    0 < completedSigmaDisplacedSourceCoefficient d 0 := by
  simpa [completedSigmaDisplacedSourceCoefficient, sigmaTaylorCoefficient] using
    completedSigmaDensity_zero_pos d hd₁ hd₂

/-- The source Bezout kernel is congruent to the Hankel matrix of the original sigma jets at
the exact positive scale two. -/
theorem completedSigmaDisplacedSource_bezout_congruence (d : ℝ)
    (hd₁ : -(1 / 2 : ℝ) < d) (hd₂ : d < (1 / 2 : ℝ))
    (oddSector : Bool) (r : ℕ) :
    coefficientBlock
        (sourceKernel (completedSigmaDisplacedSourceCoefficient d) oddSector) r =
      convolutionMatrix (completedSigmaDisplacedSourceCoefficient d) r *
        hankelMatrix (completedSigmaDisplacedMoment d)
          (if oddSector then 1 else 0) r *
        (convolutionMatrix (completedSigmaDisplacedSourceCoefficient d) r).transpose := by
  exact source_bezout_to_hankel_congruence
    (completedSigmaDisplacedSourceCoefficient d) (completedSigmaDisplacedMoment d)
    (completedSigmaDisplacedSource_recurrence d hd₁ hd₂) oddSector r

/-- The displaced-source Bézout block is congruent to the original sigma matrix at the explicit
positive scale two; its convolution factors come from the source coefficients themselves. -/
theorem completedSigmaDisplacedSource_bezout_congruence_sigmaMatrix (d : ℝ)
    (hd₁ : -(1 / 2 : ℝ) < d) (hd₂ : d < (1 / 2 : ℝ))
    (oddSector : Bool) (r : ℕ) :
    coefficientBlock
        (sourceKernel (completedSigmaDisplacedSourceCoefficient d) oddSector) r =
      convolutionMatrix (completedSigmaDisplacedSourceCoefficient d) r *
        ((2 : ℝ) • CarryMovingSigma.sigmaMatrix d
          (if oddSector then 1 else 0) r) *
        (convolutionMatrix (completedSigmaDisplacedSourceCoefficient d) r).transpose := by
  rw [completedSigmaDisplacedSource_bezout_congruence d hd₁ hd₂ oddSector r]
  rw [completedSigmaDisplacedMoment_hankel_eq_two_sigmaMatrix d
    (if oddSector then 1 else 0) r]

/-- At every finite size, the original source Bézout block is positive semidefinite exactly when
the corresponding original sigma matrix is.  The only rescaling is the positive factor two. -/
theorem completedSigmaDisplacedSource_bezout_posSemidef_iff_sigmaMatrix (d : ℝ)
    (hd₁ : -(1 / 2 : ℝ) < d) (hd₂ : d < (1 / 2 : ℝ))
    (oddSector : Bool) (r : ℕ) :
    (coefficientBlock
        (sourceKernel (completedSigmaDisplacedSourceCoefficient d) oddSector) r).PosSemidef ↔
      (CarryMovingSigma.sigmaMatrix d (if oddSector then 1 else 0) r).PosSemidef := by
  let M := CarryMovingSigma.sigmaMatrix d (if oddSector then 1 else 0) r
  have hscale : ((2 : ℝ) • M).PosSemidef ↔ M.PosSemidef := by
    constructor
    · intro h
      have h' : ((2 : ℝ)⁻¹ • ((2 : ℝ) • M)).PosSemidef :=
        h.smul (inv_nonneg.mpr (by norm_num))
      simpa [smul_smul] using h'
    · intro h
      exact h.smul (by norm_num)
  rw [source_bezout_posSemidef_iff
    (completedSigmaDisplacedSourceCoefficient d) (completedSigmaDisplacedMoment d)
    (completedSigmaDisplacedSource_recurrence d hd₁ hd₂)
    (completedSigmaDisplacedSourceCoefficient_zero_pos d hd₁ hd₂).ne'
    oddSector r]
  rw [completedSigmaDisplacedMoment_hankel_eq_two_sigmaMatrix d
    (if oddSector then 1 else 0) r]
  exact hscale

end
end CarrySigmaObstruction
