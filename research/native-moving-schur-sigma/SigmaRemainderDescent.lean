import SigmaIsolationFactorization
import SigmaZeroPairDecomposition
import SigmaPadeConvergence
import Mathlib.Analysis.Complex.Liouville

/-!
# Even Taylor descent and Cauchy control

An analytic even function of the displacement variable has a Taylor series containing only
even powers. This file packages those coefficients as a power series in the squared variable
and proves the corresponding radius bound directly from Cauchy's estimate.
-/

namespace CarrySigmaObstruction

open Filter Topology
open CarrySigmaPade
open CarrySigmaSource

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- The Taylor series in `u` obtained by retaining the even Taylor coefficients of `f(t)`. -/
def sigmaEvenTaylorSeries (f : ℂ → ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ
    (fun n => iteratedDeriv (2 * n) f 0 / ((2 * n).factorial : ℂ))

/-- The even Taylor series of an analytic even function sums back to `f(t)` near the center. -/
theorem analytic_even_taylor_series_sum
    (f : ℂ → ℂ) (hanalytic : AnalyticAt ℂ f 0)
    (heven : (fun z : ℂ => f (-z)) =ᶠ[𝓝 0] f)
    (hQradius : 0 < (sigmaEvenTaylorSeries f).radius) :
    let Q := sigmaEvenTaylorSeries f
    ∀ᶠ t : ℂ in 𝓝 0, Q.sum (t ^ 2) = f t := by
  classical
  let Q := sigmaEvenTaylorSeries f
  let T := FormalMultilinearSeries.ofScalars ℂ
    (fun n => iteratedDeriv n f 0 / (n.factorial : ℂ))
  have hodd (n : ℕ) : iteratedDeriv (2 * n + 1) f 0 = 0 := by
    have hderivEq := heven.iteratedDeriv_eq (2 * n + 1)
    have hpow : (-1 : ℂ) ^ (2 * n + 1) = -1 := by
      calc
        (-1 : ℂ) ^ (2 * n + 1) = (-1 : ℂ) ^ (2 * n) * (-1) := by rw [pow_succ]
        _ = -1 := by rw [pow_mul]; norm_num
    have hneg : -iteratedDeriv (2 * n + 1) f 0 = iteratedDeriv (2 * n + 1) f 0 := by
      simpa [iteratedDeriv_comp_neg, Nat.add_mul, hpow] using hderivEq
    have hsum : iteratedDeriv (2 * n + 1) f 0 + iteratedDeriv (2 * n + 1) f 0 = 0 := by
      rw [← neg_eq_iff_add_eq_zero, hneg]
    have hmul : (2 : ℂ) * iteratedDeriv (2 * n + 1) f 0 = 0 := by
      simpa [two_mul] using hsum
    exact (mul_eq_zero.mp hmul).resolve_left (by norm_num)
  have hTaylor : HasFPowerSeriesAt f T 0 := by
    dsimp [T]
    exact hanalytic.hasFPowerSeriesAt
  let a : ℕ → ℂ := fun n => iteratedDeriv n f 0 / (n.factorial : ℂ)
  have hTaylorSum : ∀ᶠ t : ℂ in 𝓝 0,
      HasSum (fun n => a n * t ^ n) (f t) := by
    filter_upwards [hTaylor.eventually_hasSum] with t ht
    simpa [T, a, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm] using ht
  have hQseries : HasFPowerSeriesAt Q.sum Q 0 :=
    (Q.hasFPowerSeriesOnBall hQradius).hasFPowerSeriesAt
  have hQsum : ∀ᶠ u : ℂ in 𝓝 0,
      HasSum (fun n => Q n (fun _ : Fin n => u)) (Q.sum u) := by
    simpa only [zero_add] using hQseries.eventually_hasSum
  have hsq : Filter.Tendsto (fun t : ℂ => t ^ 2) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℂ => t ^ 2) := by fun_prop
    simpa using (hc.continuousAt : ContinuousAt (fun t : ℂ => t ^ 2) 0).tendsto
  have hQsumSq : ∀ᶠ t : ℂ in 𝓝 0,
      HasSum (fun n => a (2 * n) * t ^ (2 * n)) (Q.sum (t ^ 2)) := by
    filter_upwards [hsq.eventually hQsum] with t ht
    have ht' : HasSum (fun n => Q n (fun _ : Fin n => t ^ 2)) (Q.sum (t ^ 2)) := by
      simpa only [zero_add] using ht
    convert ht' using 1
    · funext n
      symm
      simp only [Q, sigmaEvenTaylorSeries, FormalMultilinearSeries.ofScalars_apply_eq,
        smul_eq_mul, a]
      rw [pow_mul]
  have hoddSum (t : ℂ) :
      HasSum (fun n => a (2 * n + 1) * t ^ (2 * n + 1)) 0 := by
    have hterm : ∀ n, a (2 * n + 1) * t ^ (2 * n + 1) = 0 := by
      intro n
      simp [a, hodd n]
    simp [hterm]
  filter_upwards [hTaylorSum, hQsumSq] with t hTaylorAtT hEvenAtT
  let b : ℕ → ℂ := fun n => a n * t ^ n
  have hevenSum : HasSum (fun n => b (2 * n)) (Q.sum (t ^ 2)) := by
    simpa [b] using hEvenAtT
  have hoddSum' : HasSum (fun n => b (2 * n + 1)) 0 := by
    simpa [b] using hoddSum t
  have hfull := HasSum.even_add_odd (f := b) hevenSum hoddSum'
  have hfull' : HasSum (fun n => a n * t ^ n) (Q.sum (t ^ 2)) := by
    simpa [b] using hfull
  exact hfull'.unique hTaylorAtT

/-- Cauchy's estimate gives the even Taylor series in `u=t²` a radius at least `s²`. -/
theorem analytic_even_taylor_series_radius
    (f : ℂ → ℂ) (r s : ℝ)
    (hs : 0 < s) (hsr : s < r)
    (hanalytic : ∀ z : ℂ, ‖z‖ < r → AnalyticAt ℂ f z) :
    let Q := sigmaEvenTaylorSeries f
    ENNReal.ofNNReal ⟨s, le_of_lt hs⟩ ^ 2 ≤ Q.radius := by
  classical
  let Q := sigmaEvenTaylorSeries f
  let sNN : NNReal := ⟨s, le_of_lt hs⟩
  have hcontinuousClosedBall : ContinuousOn f (Metric.closedBall (0 : ℂ) s) := by
    intro z hz
    have hzNorm : ‖z‖ ≤ s := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    exact (hanalytic z (lt_of_le_of_lt hzNorm hsr)).continuousAt.continuousWithinAt
  have hcontinuousClosed : ContinuousOn f (closure (Metric.ball (0 : ℂ) s)) :=
    hcontinuousClosedBall.mono Metric.closure_ball_subset_closedBall
  have hdifferentiableBall : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) s) := by
    intro z hz
    have hz' : ‖z‖ < s := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    exact (hanalytic z (lt_trans hz' hsr)).differentiableAt.differentiableWithinAt
  have hdiffCont : DiffContOnCl ℂ f (Metric.ball (0 : ℂ) s) :=
    ⟨hdifferentiableBall, hcontinuousClosed⟩
  have hsphereCompact : IsCompact (Metric.sphere (0 : ℂ) s) := isCompact_sphere 0 s
  have hcontinuousSphere : ContinuousOn f (Metric.sphere (0 : ℂ) s) :=
    hcontinuousClosedBall.mono Metric.sphere_subset_closedBall
  obtain ⟨B, hB⟩ := hsphereCompact.exists_bound_of_continuousOn hcontinuousSphere
  let C : ℝ := max B 1
  have hCbound (z : ℂ) (hz : z ∈ Metric.sphere (0 : ℂ) s) : ‖f z‖ ≤ C :=
    (hB z hz).trans (le_max_left B 1)
  have hQbound (n : ℕ) : ‖Q n‖ * ((sNN ^ 2 : NNReal) : ℝ) ^ n ≤ C := by
    let k := 2 * n
    have hCauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
      (f := f) k hs hdiffCont hCbound
    have hfactpos : (0 : ℝ) < (k.factorial : ℝ) := by positivity
    have hsPowPos : 0 < s ^ k := pow_pos hs k
    have hpow : ((sNN ^ 2 : NNReal) : ℝ) ^ n = s ^ k := by
      change (s ^ 2) ^ n = s ^ (2 * n)
      rw [pow_mul]
    rw [hpow]
    change ‖sigmaEvenTaylorSeries f n‖ * s ^ (2 * n) ≤ C
    rw [sigmaEvenTaylorSeries, FormalMultilinearSeries.ofScalars_norm]
    have hnorm :
        ‖iteratedDeriv k f 0 / (k.factorial : ℂ)‖ =
          ‖iteratedDeriv k f 0‖ / (k.factorial : ℝ) := by simp
    rw [hnorm]
    calc
      (‖iteratedDeriv k f 0‖ / (k.factorial : ℝ)) * s ^ k ≤
          ((k.factorial : ℝ) * C / s ^ k / (k.factorial : ℝ)) * s ^ k := by gcongr
      _ = C := by field_simp [ne_of_gt hfactpos, ne_of_gt hsPowPos]
  have hQradius : ENNReal.ofNNReal sNN ^ 2 ≤ Q.radius := by
    change (↑(sNN ^ 2) : ENNReal) ≤ Q.radius
    exact Q.le_radius_of_bound C hQbound
  simpa [sNN, Q] using hQradius

/-- General analytic even-function descent, combining the local Taylor identity and the
quantitative Cauchy radius bound. -/
theorem analytic_even_has_square_series
    (f : ℂ → ℂ) (r s : ℝ)
    (hr : 0 < r) (hs : 0 < s) (hsr : s < r)
    (hanalytic : ∀ z : ℂ, ‖z‖ < r → AnalyticAt ℂ f z)
    (heven : ∀ z : ℂ, ‖z‖ < r → f (-z) = f z) :
    let Q := sigmaEvenTaylorSeries f
    ENNReal.ofNNReal ⟨s, le_of_lt hs⟩ ^ 2 ≤ Q.radius ∧
      (∀ᶠ t : ℂ in 𝓝 0, Q.sum (t ^ 2) = f t) := by
  let Q := sigmaEvenTaylorSeries f
  have hevenNhd : (fun z : ℂ => f (-z)) =ᶠ[𝓝 0] f := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with z hz
    exact heven z (by simpa [Metric.mem_ball, dist_eq_norm] using hz)
  have hradius := analytic_even_taylor_series_radius f r s hs hsr hanalytic
  let sNN : NNReal := ⟨s, le_of_lt hs⟩
  have hsNNpos : 0 < sNN := by exact_mod_cast hs
  have hsNNSqPos : 0 < sNN ^ 2 := sq_pos_of_pos hsNNpos
  have hQpos : 0 < Q.radius := by
    have hpos : (0 : ENNReal) < ENNReal.ofNNReal sNN ^ 2 := by
      rw [← ENNReal.coe_pow]
      exact ENNReal.coe_pos.mpr hsNNSqPos
    have hrad : ENNReal.ofNNReal sNN ^ 2 ≤ Q.radius := by simpa [sNN] using hradius
    exact lt_of_lt_of_le hpos hrad
  have hsum := analytic_even_taylor_series_sum f
    (hanalytic 0 (by simp [hr])) hevenNhd hQpos
  exact ⟨hradius, hsum⟩

/-- A holomorphic germ is determined by its values after the squaring map. This avoids choosing
a branch of the square root when lifting a local identity from `t²` back to `u`. -/
theorem analytic_eventually_zero_of_comp_square
    (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0)
    (hzero : ∀ᶠ t : ℂ in 𝓝 0, f (t ^ 2) = 0) :
    ∀ᶠ u : ℂ in 𝓝 0, f u = 0 := by
  have hsq : AnalyticAt ℂ (fun z : ℂ => z ^ 2) 0 := by fun_prop
  have hsqOrder : analyticOrderAt (fun z : ℂ => z ^ 2) 0 = 2 := by
    have hfun : (fun z : ℂ => z ^ 2) = (fun z : ℂ => z) ^ 2 := by
      funext z
      rfl
    rw [hfun, analyticOrderAt_pow
      (f := fun z : ℂ => z) (z₀ := (0 : ℂ))
      (analyticAt_id : AnalyticAt ℂ (fun z : ℂ => z) 0) 2]
    change 2 • analyticOrderAt id 0 = 2
    rw [analyticOrderAt_id]
    norm_num
  have hf' : AnalyticAt ℂ f ((fun z : ℂ => z ^ 2) 0) := by simpa using hf
  have hcompOrder := AnalyticAt.analyticOrderAt_comp hf' hsq
  have hcompOrder' : analyticOrderAt (fun z : ℂ => f (z ^ 2)) 0 =
      analyticOrderAt f 0 * 2 := by
    simpa [Function.comp_def, hsqOrder] using hcompOrder
  have hcompZero : ∀ᶠ t : ℂ in 𝓝 0, (fun z : ℂ => f (z ^ 2)) t = 0 := by
    simpa using hzero
  have hcompTop : analyticOrderAt (fun z : ℂ => f (z ^ 2)) 0 = ⊤ :=
    analyticOrderAt_eq_top.mpr hcompZero
  have hmulTop : analyticOrderAt f 0 * 2 = ⊤ := by
    exact hcompOrder'.symm.trans hcompTop
  have hfTop : analyticOrderAt f 0 = ⊤ := by
    rcases (WithTop.mul_eq_top_iff (a := analyticOrderAt f 0)
      (b := (2 : ℕ∞))).mp hmulTop with ⟨_, htwoTop⟩ | ⟨hfTop, _⟩
    · exact False.elim ((ENat.coe_ne_top 2) htwoTop)
    · exact hfTop
  exact analyticOrderAt_eq_top.mp hfTop

/-- Complexification of the two-pole moment is the symmetric sum of the two geometric
coefficients. -/
lemma twoPoleMoment_complex_eq (m : ℝ) (ζ : ℂ) (n : ℕ) :
    (twoPoleMoment m ζ n : ℂ) =
      ((m : ℂ) / 2) * (ζ ^ (n + 1) + (star ζ) ^ (n + 1)) := by
  rw [twoPoleMoment]
  have hstar : (star ζ) ^ (n + 1) = star (ζ ^ (n + 1)) := by simp
  rw [hstar]
  let z : ℂ := ζ ^ (n + 1)
  change (↑(m * z.re) : ℂ) = ((m : ℂ) / 2) * (z + star z)
  calc
    (↑(m * z.re) : ℂ) = (m : ℂ) * ↑z.re := by push_cast; ring
    _ = ((m : ℂ) / 2) * ↑(2 * z.re) := by push_cast; ring
    _ = ((m : ℂ) / 2) * (z + star z) := by
      have hadd := Complex.add_conj z
      exact (congrArg (fun w : ℂ => ((m : ℂ) / 2) * w) hadd).symm

/-- The rational two-pole model has precisely the declared model series as its Taylor series. -/
theorem sigmaZeroPairRationalModel_hasFPowerSeriesAt (m : ℝ) (ζ : ℂ) :
    HasFPowerSeriesAt (sigmaZeroPairRationalModel m ζ)
      (sigmaZeroPairModelSeries m ζ) 0 := by
  classical
  let P := sigmaZeroPairModelSeries m ζ
  let M : ℝ := max ‖ζ‖ 1
  let r : ℝ := (2 * M)⁻¹
  let rNN : NNReal := ⟨r, le_of_lt (by dsimp [r]; positivity)⟩
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right ‖ζ‖ 1)
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hrNNpos : 0 < rNN := by exact_mod_cast hrpos
  have hζsmall : ‖ζ‖ * r ≤ 1 := by
    calc
      ‖ζ‖ * r ≤ M * r := mul_le_mul_of_nonneg_right (le_max_left ‖ζ‖ 1) (le_of_lt hrpos)
      _ = 1 / 2 := by dsimp [r, M]; field_simp
      _ ≤ 1 := by norm_num
  have hbound (n : ℕ) : ‖P n‖ * (rNN : ℝ) ^ n ≤ max (|m| * M) 1 := by
    have hnormP : ‖P n‖ = |twoPoleMoment m ζ n| := by
      simp [P, sigmaZeroPairModelSeries]
    have hmoment : |twoPoleMoment m ζ n| ≤ |m| * ‖ζ‖ ^ (n + 1) := by
      rw [twoPoleMoment, abs_mul]
      exact mul_le_mul_of_nonneg_left
        (by simpa [norm_pow] using Complex.abs_re_le_norm (ζ ^ (n + 1))) (abs_nonneg m)
    have hpow : (‖ζ‖ * r) ^ n ≤ 1 :=
      pow_le_one₀ (mul_nonneg (norm_nonneg _) (le_of_lt hrpos)) hζsmall
    have hzprod : ‖ζ‖ * (‖ζ‖ * r) ^ n ≤ M := by
      calc
        ‖ζ‖ * (‖ζ‖ * r) ^ n ≤ M * 1 :=
          mul_le_mul (le_max_left ‖ζ‖ 1) hpow
            (pow_nonneg (mul_nonneg (norm_nonneg _) (le_of_lt hrpos)) n)
            (le_of_lt hMpos)
        _ = M := by ring
    rw [hnormP]
    calc
      |twoPoleMoment m ζ n| * (rNN : ℝ) ^ n ≤
          (|m| * ‖ζ‖ ^ (n + 1)) * r ^ n :=
            mul_le_mul_of_nonneg_right hmoment (pow_nonneg (le_of_lt hrpos) n)
      _ = |m| * (‖ζ‖ * (‖ζ‖ * r) ^ n) := by rw [pow_succ]; ring
      _ ≤ |m| * M := mul_le_mul_of_nonneg_left hzprod (abs_nonneg m)
      _ ≤ max (|m| * M) 1 := le_max_left _ _
  have hPradius : ENNReal.ofNNReal rNN ≤ P.radius := by
    exact P.le_radius_of_bound (max (|m| * M) 1) hbound
  have hPpos : 0 < P.radius := lt_of_lt_of_le (ENNReal.coe_pos.mpr hrNNpos) hPradius
  have hPseries : HasFPowerSeriesAt P.sum P 0 :=
    (P.hasFPowerSeriesOnBall hPpos).hasFPowerSeriesAt
  have hPsum : ∀ᶠ u : ℂ in 𝓝 0,
      HasSum (fun n => P n (fun _ : Fin n => u)) (P.sum u) := by
    simpa only [zero_add] using hPseries.eventually_hasSum
  have hsmall : ∀ᶠ u : ℂ in 𝓝 0, ‖ζ * u‖ < 1 ∧ ‖star ζ * u‖ < 1 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hrpos] with u hu
    have hu' : ‖u‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hu
    constructor
    · calc
        ‖ζ * u‖ = ‖ζ‖ * ‖u‖ := norm_mul _ _
        _ ≤ M * ‖u‖ := mul_le_mul_of_nonneg_right
          (le_max_left ‖ζ‖ 1) (norm_nonneg u)
        _ < M * r := mul_lt_mul_of_pos_left hu' hMpos
        _ = 1 / 2 := by dsimp [r, M]; field_simp
        _ < 1 := by norm_num
    · calc
        ‖star ζ * u‖ = ‖ζ‖ * ‖u‖ := by simp
        _ ≤ M * ‖u‖ := mul_le_mul_of_nonneg_right
          (le_max_left ‖ζ‖ 1) (norm_nonneg u)
        _ < M * r := mul_lt_mul_of_pos_left hu' hMpos
        _ = 1 / 2 := by dsimp [r, M]; field_simp
        _ < 1 := by norm_num
  have hgeomSum : ∀ᶠ u : ℂ in 𝓝 0,
      HasSum (fun n => P n (fun _ : Fin n => u)) (sigmaZeroPairRationalModel m ζ u) := by
    filter_upwards [hsmall] with u hu
    have hgeom₁ := (hasSum_geometric_of_norm_lt_one hu.1).mul_left ζ |>.mul_left ((m : ℂ) / 2)
    have hgeom₂ := (hasSum_geometric_of_norm_lt_one hu.2).mul_left (star ζ) |>.mul_left ((m : ℂ) / 2)
    have hsum := hgeom₁.add hgeom₂
    have hterms (n : ℕ) : P n (fun _ : Fin n => u) =
        ((m : ℂ) / 2) * (ζ * (ζ * u) ^ n) +
          ((m : ℂ) / 2) * (star ζ * (star ζ * u) ^ n) := by
      simp only [P, sigmaZeroPairModelSeries, FormalMultilinearSeries.ofScalars_apply_eq,
        smul_eq_mul]
      rw [twoPoleMoment_complex_eq, pow_succ, pow_succ, mul_pow, mul_pow]
      ring
    have hsum' : HasSum (fun n => P n (fun _ : Fin n => u))
        ((m : ℂ) / 2 * (ζ * (1 - ζ * u)⁻¹) +
          (m : ℂ) / 2 * (star ζ * (1 - star ζ * u)⁻¹)) :=
      hsum.congr_fun hterms
    have hvalue : sigmaZeroPairRationalModel m ζ u =
        ((m : ℂ) / 2) * (ζ * (1 - ζ * u)⁻¹) +
          ((m : ℂ) / 2) * (star ζ * (1 - star ζ * u)⁻¹) := by
      simp only [sigmaZeroPairRationalModel, div_eq_mul_inv]
      ring
    rw [hvalue]
    exact hsum'
  have hEq : ∀ᶠ u : ℂ in 𝓝 0, P.sum u = sigmaZeroPairRationalModel m ζ u := by
    filter_upwards [hPsum, hgeomSum] with u hP hmodel
    exact hP.unique hmodel
  exact hPseries.congr hEq

/-- Product of the two even linear factors in the squared variable. -/
def sigmaTwoPoleFactor (ζ : ℂ) (m : ℕ) (t : ℂ) : ℂ :=
  (1 - ζ * t ^ 2) ^ m * (1 - star ζ * t ^ 2) ^ m

/-- The logarithmic derivative of the two-pole factor is exactly the rational model. -/
theorem sigmaTwoPoleFactor_logDerivative (m : ℕ) (ζ t : ℂ)
    (hm : 0 < m) (ht : t ≠ 0)
    (hA : 1 - ζ * t ^ 2 ≠ 0) (hB : 1 - star ζ * t ^ 2 ≠ 0) :
    -deriv (sigmaTwoPoleFactor ζ m) t /
        (4 * t * sigmaTwoPoleFactor ζ m t) =
      sigmaZeroPairRationalModel (m : ℝ) ζ (t ^ 2) := by
  let A : ℂ → ℂ := fun z => 1 - ζ * z ^ 2
  let B : ℂ → ℂ := fun z => 1 - star ζ * z ^ 2
  have hAderiv : deriv A t = -(2 * ζ * t) := by
    have hsq : HasDerivAt (fun z : ℂ => z ^ 2) (2 * t) t := by
      change HasDerivAt (id ^ 2) (2 * t) t
      simpa using (hasDerivAt_id t).pow 2
    have hscaled := HasDerivAt.const_mul ζ hsq
    have hAat : HasDerivAt A (-(ζ * (2 * t))) t := by
      simpa [A] using (HasDerivAt.const_sub (1 : ℂ) hscaled)
    rw [hAat.deriv]
    ring
  have hBderiv : deriv B t = -(2 * star ζ * t) := by
    have hsq : HasDerivAt (fun z : ℂ => z ^ 2) (2 * t) t := by
      change HasDerivAt (id ^ 2) (2 * t) t
      simpa using (hasDerivAt_id t).pow 2
    have hscaled := HasDerivAt.const_mul (star ζ) hsq
    have hBat : HasDerivAt B (-((star ζ) * (2 * t))) t := by
      simpa [B] using (HasDerivAt.const_sub (1 : ℂ) hscaled)
    rw [hBat.deriv]
    ring
  have hAdiff : DifferentiableAt ℂ A t := by fun_prop
  have hBdiff : DifferentiableAt ℂ B t := by fun_prop
  have hfactorDeriv : deriv (sigmaTwoPoleFactor ζ m) t =
      ((m : ℂ) * A t ^ (m - 1) * deriv A t) * B t ^ m +
        A t ^ m * ((m : ℂ) * B t ^ (m - 1) * deriv B t) := by
    change deriv (A ^ m * B ^ m) t = _
    rw [deriv_mul (hAdiff.pow m) (hBdiff.pow m), deriv_pow hAdiff m,
      deriv_pow hBdiff m]
    change ↑m * A t ^ (m - 1) * deriv A t * B t ^ m +
        A t ^ m * (↑m * B t ^ (m - 1) * deriv B t) = _
    rfl
  have hA0 : A t ≠ 0 := by simpa [A] using hA
  have hB0 : B t ≠ 0 := by simpa [B] using hB
  have hm' : m - 1 + 1 = m := Nat.sub_add_cancel hm
  have hApow : A t ^ m = A t ^ (m - 1) * A t := by
    rw [← pow_succ, hm']
  have hBpow : B t ^ m = B t ^ (m - 1) * B t := by
    rw [← pow_succ, hm']
  rw [hfactorDeriv, hAderiv, hBderiv]
  change -(((m : ℂ) * A t ^ (m - 1) * (-(2 * ζ * t)) * B t ^ m) +
      A t ^ m * ((m : ℂ) * B t ^ (m - 1) * (-(2 * star ζ * t)))) /
      (4 * t * (A t ^ m * B t ^ m)) =
    ((m : ℂ) / 2) * (ζ / A t + star ζ / B t)
  rw [hApow, hBpow]
  field_simp [ht, hA0, hB0]
  ring

/-- The native first signed pole factor is the two-pole factor with `ζ=τ⁻²`. -/
theorem sigmaDisplacedFirstPoleFactor_eq_twoPoleFactor (τ : ℂ) (m : ℕ) :
    sigmaDisplacedFirstPoleFactor τ m =
      sigmaTwoPoleFactor (τ ^ (-2 : ℤ)) m := by
  funext t
  have hinv : τ ^ (-2 : ℤ) = (τ ^ 2)⁻¹ := by
    rw [zpow_neg]
    rfl
  have hstarinv : star (τ ^ (-2 : ℤ)) = ((star τ) ^ 2)⁻¹ := by
    simp [zpow_neg]
    rfl
  have hfirst : t ^ 2 / τ ^ 2 = τ ^ (-2 : ℤ) * t ^ 2 := by
    rw [div_eq_mul_inv, ← hinv]
    ring
  have hsecond : t ^ 2 / (star τ) ^ 2 = ((star τ) ^ 2)⁻¹ * t ^ 2 := by
    rw [div_eq_mul_inv]
    ring
  change (1 - t ^ 2 / τ ^ 2) ^ m *
      (1 - t ^ 2 / (star τ) ^ 2) ^ m =
    (1 - τ ^ (-2 : ℤ) * t ^ 2) ^ m *
      (1 - star (τ ^ (-2 : ℤ)) * t ^ 2) ^ m
  rw [hfirst, hsecond, hstarinv]

/-- Logarithmic differentiation turns a product into a sum on its nonzero locus. -/
lemma neg_deriv_mul_div_eq_add (P H : ℂ → ℂ) (t : ℂ)
    (hPdiff : DifferentiableAt ℂ P t) (hHdiff : DifferentiableAt ℂ H t)
    (ht : t ≠ 0) (hP : P t ≠ 0) (hH : H t ≠ 0) :
    -deriv (fun z : ℂ => P z * H z) t / (4 * t * (P t * H t)) =
      -deriv P t / (4 * t * P t) + -deriv H t / (4 * t * H t) := by
  change -deriv (P * H) t / (4 * t * (P t * H t)) = _
  rw [deriv_mul hPdiff hHdiff]
  field_simp [ht, hP, hH]
  ring

/-- The native four-root factor has the rational two-pole logarithmic derivative. -/
theorem sigmaDisplacedFirstPoleFactor_logDerivative (τ : ℂ) (m : ℕ) (t : ℂ)
    (hm : 0 < m) (ht : t ≠ 0)
    (hP : sigmaDisplacedFirstPoleFactor τ m t ≠ 0) :
    -deriv (sigmaDisplacedFirstPoleFactor τ m) t /
        (4 * t * sigmaDisplacedFirstPoleFactor τ m t) =
      sigmaZeroPairRationalModel (m : ℝ) (τ ^ (-2 : ℤ)) (t ^ 2) := by
  let ζ : ℂ := τ ^ (-2 : ℤ)
  have hfactor := sigmaDisplacedFirstPoleFactor_eq_twoPoleFactor τ m
  have hmodel : sigmaTwoPoleFactor ζ m t ≠ 0 := by
    intro hz
    apply hP
    simpa [ζ, hfactor] using hz
  have hA : 1 - ζ * t ^ 2 ≠ 0 := by
    intro hz
    apply hmodel
    simp [sigmaTwoPoleFactor, hz, hm.ne']
  have hB : 1 - star ζ * t ^ 2 ≠ 0 := by
    intro hz
    apply hmodel
    change (1 - ζ * t ^ 2) ^ m * (1 - star ζ * t ^ 2) ^ m = 0
    rw [hz]
    simp [hm.ne']
  have hlog := sigmaTwoPoleFactor_logDerivative m ζ t hm ht hA hB
  simpa [ζ, hfactor] using hlog

/-- Zero isolation constructs the even analytic remainder and the local identity behind the
two-pole decomposition. The identity is derived from the native differential equation and the
source quotient; it is not an input assumption. -/
theorem completedNative_sigmaRemainder_local_of_isolation
    (d γ r : ℝ) (m : ℕ)
    (hisolation : SigmaDisplacedProductIsolation d γ r m) :
    ∃ H q : ℂ → ℂ,
      (∀ z ∈ Metric.ball 0 r, AnalyticAt ℂ H z) ∧
      (∀ z ∈ Metric.ball 0 r, H z ≠ 0) ∧
      (∀ z ∈ Metric.ball 0 r, H (-z) = H z) ∧
      (∀ᶠ z : ℂ in 𝓝 0, deriv H z = z * q z) ∧
      AnalyticOnNhd ℂ (sigmaDisplacedLogRemainderT H q) (Metric.ball 0 r) ∧
      (∀ z ∈ Metric.ball 0 r,
        sigmaDisplacedLogRemainderT H q (-z) = sigmaDisplacedLogRemainderT H q z) ∧
      (∀ᶠ t : ℂ in 𝓝 0,
        completedSigmaLogJetComplexGeneratingFunction d (t ^ 2) =
          sigmaZeroPairRationalModel (m : ℝ)
            (((γ : ℂ) + Complex.I * (d : ℂ)) ^ (-2 : ℤ)) (t ^ 2) +
          sigmaDisplacedLogRemainderT H q t) := by
  classical
  let τ : ℂ := (γ : ℂ) + Complex.I * (d : ℂ)
  let P : ℂ → ℂ := sigmaDisplacedFirstPoleFactor τ m
  let ζ : ℂ := τ ^ (-2 : ℤ)
  obtain ⟨H, hHanalytic, hHfactor, hHnonzero, hHeven, hHderiv0⟩ :=
    completedNativeDisplacedProduct_factorization_of_isolation d γ r m hisolation
  have hτ : τ ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    have hreal : γ = 0 := by simpa [τ] using hre
    linarith [hisolation.height_pos]
  have hd₁ : -(1 / 2 : ℝ) < d := by linarith [hisolation.displacement_pos]
  have hd₂ : d < (1 / 2 : ℝ) := by linarith [hisolation.displacement_lt_quarter]
  have hnative := completedNativeDisplacedProductContinuation_eq_native_eventually d hd₁ hd₂
  have hball : ∀ᶠ t : ℂ in 𝓝 0, t ∈ Metric.ball 0 r :=
    Metric.ball_mem_nhds 0 hisolation.radius_pos
  have hsourceFactor : displacedProductC d =ᶠ[𝓝 0] (fun t => P t * H t) := by
    filter_upwards [hnative, hball] with t hnativeT htball
    calc
      displacedProductC d t = completedNativeDisplacedProductContinuation d t := hnativeT.symm
      _ = P t * H t := by simpa only [P, τ] using hHfactor t htball
  have hsourceDeriv := hsourceFactor.deriv
  have hH0 : H 0 ≠ 0 := hHnonzero 0 (Metric.mem_ball_self hisolation.radius_pos)
  have hHanalytic0 : AnalyticAt ℂ H 0 :=
    hHanalytic 0 (Metric.mem_ball_self hisolation.radius_pos)
  have hHderivAnalytic : AnalyticAt ℂ (deriv H) 0 := hHanalytic0.deriv
  obtain ⟨q, hqanalytic, hqfactor⟩ := analyticAt_factor_by_id_of_zero
    (deriv H) hHderivAnalytic hHderiv0
  have hremAnalytic := sigmaDisplacedLogRemainderT_analyticOnNhd r
    hisolation.radius_pos H q hHanalytic hHnonzero hqanalytic hqfactor
  have hremEven := sigmaDisplacedLogRemainderT_even r H q
    hHanalytic hHnonzero hHeven
  have hP0 : P 0 ≠ 0 := by simp [P, sigmaDisplacedFirstPoleFactor]
  have hPcontinuous : ContinuousAt P 0 := by
    change ContinuousAt (sigmaDisplacedFirstPoleFactor τ m) 0
    fun_prop [sigmaDisplacedFirstPoleFactor]
  have hPne : ∀ᶠ t : ℂ in 𝓝 0, P t ≠ 0 := hPcontinuous.eventually_ne hP0
  have hHne : ∀ᶠ t : ℂ in 𝓝 0, H t ≠ 0 := by
    filter_upwards [hball] with t ht
    exact hHnonzero t ht
  have hGseries := completedSigmaLogJetComplexGeneratingFunction_hasFPowerSeriesAt
    d hd₁ hd₂
  have hGanalytic : AnalyticAt ℂ (completedSigmaLogJetComplexGeneratingFunction d) 0 :=
    hGseries.analyticAt
  have hmodelSeries := sigmaZeroPairRationalModel_hasFPowerSeriesAt (m : ℝ) ζ
  have hmodelAnalytic : AnalyticAt ℂ (sigmaZeroPairRationalModel (m : ℝ) ζ) 0 :=
    hmodelSeries.analyticAt
  have hsq : AnalyticAt ℂ (fun t : ℂ => t ^ 2) 0 := by fun_prop
  have hGsq : AnalyticAt ℂ
      (fun t : ℂ => completedSigmaLogJetComplexGeneratingFunction d (t ^ 2)) 0 :=
    AnalyticAt.comp_of_eq (g := completedSigmaLogJetComplexGeneratingFunction d)
      (f := fun t : ℂ => t ^ 2) (y := (0 : ℂ)) (x := (0 : ℂ)) hGanalytic hsq (by simp)
  have hmodelsq : AnalyticAt ℂ
      (fun t : ℂ => sigmaZeroPairRationalModel (m : ℝ) ζ (t ^ 2)) 0 :=
    AnalyticAt.comp_of_eq (g := sigmaZeroPairRationalModel (m : ℝ) ζ)
      (f := fun t : ℂ => t ^ 2) (y := (0 : ℂ)) (x := (0 : ℂ)) hmodelAnalytic hsq (by simp)
  have hrem0 : AnalyticAt ℂ (sigmaDisplacedLogRemainderT H q) 0 :=
    hremAnalytic 0 (Metric.mem_ball_self hisolation.radius_pos)
  let E : ℂ → ℂ := fun t =>
    completedSigmaLogJetComplexGeneratingFunction d (t ^ 2) -
      sigmaZeroPairRationalModel (m : ℝ) ζ (t ^ 2) - sigmaDisplacedLogRemainderT H q t
  have hEanalytic : AnalyticAt ℂ E 0 := by
    dsimp [E]
    exact (hGsq.sub hmodelsq).sub hrem0
  have hODE := displacedProductC_local_differentialEquation d hd₁ hd₂
  have hpunctured : ∀ᶠ t : ℂ in 𝓝[≠] 0,
      completedSigmaLogJetComplexGeneratingFunction d (t ^ 2) =
        sigmaZeroPairRationalModel (m : ℝ) ζ (t ^ 2) +
          sigmaDisplacedLogRemainderT H q t := by
    filter_upwards [hODE.filter_mono nhdsWithin_le_nhds,
      hsourceFactor.filter_mono nhdsWithin_le_nhds,
      hsourceDeriv.filter_mono nhdsWithin_le_nhds,
      hPne.filter_mono nhdsWithin_le_nhds,
      hHne.filter_mono nhdsWithin_le_nhds,
      hball.filter_mono nhdsWithin_le_nhds,
      eventually_mem_nhdsWithin] with t hODEt hsourceT hsourceDerivT hPnonzero hHnonzero htball htmem
    have ht : t ≠ 0 := by simpa using htmem
    have hDnonzero : displacedProductC d t ≠ 0 := by
      rw [hsourceT]
      exact mul_ne_zero hPnonzero hHnonzero
    have hGformula : completedSigmaLogJetComplexGeneratingFunction d (t ^ 2) =
        -deriv (displacedProductC d) t / (4 * t * displacedProductC d t) := by
      field_simp [ht, hDnonzero]
      linear_combination hODEt
    have hlogProduct := neg_deriv_mul_div_eq_add P H t
      (by
        change DifferentiableAt ℂ (sigmaDisplacedFirstPoleFactor τ m) t
        fun_prop [sigmaDisplacedFirstPoleFactor])
      (hHanalytic t htball).differentiableAt ht hPnonzero hHnonzero
    calc
      completedSigmaLogJetComplexGeneratingFunction d (t ^ 2) =
          -deriv (fun z : ℂ => P z * H z) t / (4 * t * (P t * H t)) := by
            rw [hGformula, hsourceDerivT, hsourceT]
      _ = -deriv P t / (4 * t * P t) + -deriv H t / (4 * t * H t) := hlogProduct
      _ = sigmaZeroPairRationalModel (m : ℝ) ζ (t ^ 2) +
            sigmaDisplacedLogRemainderT H q t := by
          rw [sigmaDisplacedFirstPoleFactor_logDerivative τ m t
            hisolation.multiplicity_pos ht hPnonzero]
          simp [sigmaDisplacedLogRemainderT, ht, ζ, τ]
  have hEeventually : ∀ᶠ t : ℂ in 𝓝 0, E t = 0 := by
    have hfreq : ∃ᶠ t : ℂ in 𝓝[≠] 0, E t = 0 := by
      have hevent : ∀ᶠ t : ℂ in 𝓝[≠] 0, E t = 0 := by
        filter_upwards [hpunctured] with t ht
        dsimp [E]
        rw [ht]
        ring
      exact hevent.frequently
    exact hEanalytic.frequently_zero_iff_eventually_zero.mp hfreq
  have hlocal : ∀ᶠ t : ℂ in 𝓝 0,
      completedSigmaLogJetComplexGeneratingFunction d (t ^ 2) =
        sigmaZeroPairRationalModel (m : ℝ) ζ (t ^ 2) +
          sigmaDisplacedLogRemainderT H q t := by
    filter_upwards [hEeventually] with t ht
    dsimp [E] at ht
    linear_combination ht
  exact ⟨H, q, hHanalytic, hHnonzero, hHeven, hqfactor, hremAnalytic, hremEven,
    hlocal⟩

/-- Exact descent to `u=t²`: under the source zero-isolation certificate, the even
logarithmic-derivative remainder has the original coefficientwise residual series and enough
radius to lie strictly outside the two-pole model radius. -/
theorem completedNative_sigmaRemainder_square_decomposition_of_isolation
    (d γ r : ℝ) (m : ℕ)
    (hisolation : SigmaDisplacedProductIsolation d γ r m) :
    ∃ C η : ℝ, 0 < C ∧ 0 < η ∧
      η < ‖((γ : ℂ) + Complex.I * (d : ℂ)) ^ (-2 : ℤ)‖ ∧
      (∀ n, (completedSigmaLogJet d n : ℂ) =
        (twoPoleMoment (m : ℝ) (((γ : ℂ) + Complex.I * (d : ℂ)) ^ (-2 : ℤ)) n : ℂ) +
          (sigmaZeroPairRemainderMoment d (m : ℝ)
            (((γ : ℂ) + Complex.I * (d : ℂ)) ^ (-2 : ℤ)) n : ℂ)) ∧
      ∀ n, |sigmaZeroPairRemainderMoment d (m : ℝ)
        (((γ : ℂ) + Complex.I * (d : ℂ)) ^ (-2 : ℤ)) n| ≤ C * η ^ n := by
  classical
  let τ : ℂ := (γ : ℂ) + Complex.I * (d : ℂ)
  let ζ : ℂ := τ ^ (-2 : ℤ)
  let s : ℝ := (‖τ‖ + r) / 2
  have hτ : τ ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    have hreal : γ = 0 := by simpa [τ] using hre
    linarith [hisolation.height_pos]
  have hd₁ : -(1 / 2 : ℝ) < d := by linarith [hisolation.displacement_pos]
  have hd₂ : d < (1 / 2 : ℝ) := by linarith [hisolation.displacement_lt_quarter]
  have hnormτr : ‖τ‖ < r := by simpa [τ] using hisolation.first_pair_inside
  have hs : ‖τ‖ < s := by dsimp [s]; linarith
  have hsr : s < r := by dsimp [s]; linarith
  have hspos : 0 < s := by
    linarith [hs, norm_nonneg τ]
  obtain ⟨H, q, hHanalytic, hHnonzero, hHeven, _hqfactor, hremAnalytic, hremEven,
    hlocal⟩ := completedNative_sigmaRemainder_local_of_isolation d γ r m hisolation
  let f : ℂ → ℂ := sigmaDisplacedLogRemainderT H q
  have hanalytic : ∀ z : ℂ, ‖z‖ < r → AnalyticAt ℂ f z := by
    intro z hz
    exact hremAnalytic z (by simpa [Metric.mem_ball, dist_eq_norm] using hz)
  have heven : ∀ z : ℂ, ‖z‖ < r → f (-z) = f z := by
    intro z hz
    exact hremEven z (by simpa [Metric.mem_ball, dist_eq_norm] using hz)
  have hsquare := analytic_even_has_square_series f r s
    hisolation.radius_pos hspos hsr hanalytic heven
  let Q : FormalMultilinearSeries ℂ ℂ ℂ := sigmaEvenTaylorSeries f
  have hQradius : ENNReal.ofNNReal ⟨s, le_of_lt hspos⟩ ^ 2 ≤ Q.radius := by
    simpa [Q, f] using hsquare.1
  have hQsum : ∀ᶠ t : ℂ in 𝓝 0, Q.sum (t ^ 2) = f t := by
    simpa [Q, f] using hsquare.2
  let sNN : NNReal := ⟨s, le_of_lt hspos⟩
  let aNN : NNReal := ‖τ‖₊ ^ 2
  let ρ : NNReal := (aNN + sNN ^ 2) / 2
  have hnormτlt : ‖τ‖₊ < sNN := by
    exact_mod_cast hs
  have hnormτsq : aNN < sNN ^ 2 := by
    change ‖τ‖₊ ^ 2 < sNN ^ 2
    have hltReal : (‖τ‖₊ : ℝ) < (sNN : ℝ) := by exact_mod_cast hnormτlt
    have hsqReal : (‖τ‖₊ : ℝ) ^ 2 < (sNN : ℝ) ^ 2 := by
      nlinarith [hltReal, show 0 ≤ (‖τ‖₊ : ℝ) by positivity]
    exact_mod_cast hsqReal
  have hmodelRadiusNN : 1 / ‖ζ‖₊ = aNN := by
    have hnormζ : ‖ζ‖₊ = (‖τ‖₊ ^ 2)⁻¹ := by
      simp [ζ, nnnorm_zpow, zpow_neg]
      rfl
    calc
      1 / ‖ζ‖₊ = 1 / ((‖τ‖₊ ^ 2)⁻¹) := by rw [hnormζ]
      _ = ‖τ‖₊ ^ 2 := by simp
      _ = aNN := by rfl
  have hρlower : 1 / ‖ζ‖₊ < ρ := by
    rw [hmodelRadiusNN]
    dsimp [ρ]
    linarith
  have hρupper : ρ < sNN ^ 2 := by
    dsimp [ρ]
    linarith
  have hsNNpos : 0 < sNN := by exact_mod_cast hspos
  have hsNNsqpos : 0 < sNN ^ 2 := sq_pos_of_pos hsNNpos
  have hQpos : 0 < Q.radius := by
    have hpos : (0 : ENNReal) < ENNReal.ofNNReal (sNN ^ 2) :=
      ENNReal.coe_pos.mpr hsNNsqpos
    have hQradius' : ENNReal.ofNNReal (sNN ^ 2) ≤ Q.radius := by
      simpa [sNN, ← ENNReal.coe_pow] using hQradius
    exact lt_of_lt_of_le hpos hQradius'
  have hQseries : HasFPowerSeriesAt Q.sum Q 0 :=
    (Q.hasFPowerSeriesOnBall hQpos).hasFPowerSeriesAt
  have hGseries := completedSigmaLogJetComplexGeneratingFunction_hasFPowerSeriesAt
    d hd₁ hd₂
  have hmodel := sigmaZeroPairRationalModel_hasFPowerSeriesAt (m : ℝ) ζ
  have hQanalytic : AnalyticAt ℂ Q.sum 0 := hQseries.analyticAt
  have hGanalytic : AnalyticAt ℂ (completedSigmaLogJetComplexGeneratingFunction d) 0 :=
    hGseries.analyticAt
  have hmodelAnalytic : AnalyticAt ℂ (sigmaZeroPairRationalModel (m : ℝ) ζ) 0 :=
    hmodel.analyticAt
  let E : ℂ → ℂ := fun u =>
    completedSigmaLogJetComplexGeneratingFunction d u -
      sigmaZeroPairRationalModel (m : ℝ) ζ u - Q.sum u
  have hEanalytic : AnalyticAt ℂ E 0 := by
    dsimp [E]
    exact (hGanalytic.sub hmodelAnalytic).sub hQanalytic
  have hcompzero : ∀ᶠ t : ℂ in 𝓝 0, E (t ^ 2) = 0 := by
    filter_upwards [hlocal, hQsum] with t hloc hsum
    dsimp [E]
    rw [hloc, hsum]
    ring
  have hEzero := analytic_eventually_zero_of_comp_square E hEanalytic hcompzero
  have hdecomp : ∀ᶠ u : ℂ in 𝓝 0,
      completedSigmaLogJetComplexGeneratingFunction d u =
        sigmaZeroPairRationalModel (m : ℝ) ζ u + Q.sum u := by
    filter_upwards [hEzero] with u hu
    dsimp [E] at hu
    linear_combination hu
  have hQeq : Q = sigmaZeroPairRemainderSeries d (m : ℝ) ζ := by
    have hseriesEq : completedSigmaLogJetComplexSeries d =
        sigmaZeroPairModelSeries (m : ℝ) ζ + Q :=
      hGseries.eq_formalMultilinearSeries_of_eventually (hmodel.add hQseries) hdecomp
    have hcoeff (n : ℕ) :
        Q n (fun _ : Fin n => (1 : ℂ)) =
          (sigmaZeroPairRemainderMoment d (m : ℝ) ζ n : ℂ) := by
      have heval := congrArg (fun S : FormalMultilinearSeries ℂ ℂ ℂ =>
        S n (fun _ : Fin n => (1 : ℂ))) hseriesEq
      have heval' : (completedSigmaLogJet d n : ℂ) =
          (twoPoleMoment (m : ℝ) ζ n : ℂ) + Q n (fun _ : Fin n => (1 : ℂ)) := by
        simpa [completedSigmaLogJetComplexSeries, sigmaZeroPairModelSeries,
          FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] using heval
      calc
        Q n (fun _ : Fin n => (1 : ℂ)) =
            ((twoPoleMoment (m : ℝ) ζ n : ℂ) +
              Q n (fun _ : Fin n => (1 : ℂ))) - (twoPoleMoment (m : ℝ) ζ n : ℂ) := by ring
        _ = (completedSigmaLogJet d n : ℂ) - (twoPoleMoment (m : ℝ) ζ n : ℂ) := by
          rw [← heval']
        _ = (sigmaZeroPairRemainderMoment d (m : ℝ) ζ n : ℂ) := by
          simp [sigmaZeroPairRemainderMoment]
    have hscalar (n : ℕ) :
        iteratedDeriv (2 * n) f 0 / ((2 * n).factorial : ℂ) =
          (sigmaZeroPairRemainderMoment d (m : ℝ) ζ n : ℂ) := by
      simpa [Q, sigmaEvenTaylorSeries, FormalMultilinearSeries.ofScalars_apply_eq,
        smul_eq_mul] using hcoeff n
    apply FormalMultilinearSeries.ext
    intro n
    change (iteratedDeriv (2 * n) f 0 / ((2 * n).factorial : ℂ)) •
        ContinuousMultilinearMap.mkPiAlgebraFin ℂ n ℂ =
      (sigmaZeroPairRemainderMoment d (m : ℝ) ζ n : ℂ) •
        ContinuousMultilinearMap.mkPiAlgebraFin ℂ n ℂ
    rw [hscalar n]
  have hmodelRadius : ENNReal.ofNNReal (1 / ‖ζ‖₊) < ENNReal.ofNNReal ρ := by
    exact_mod_cast hρlower
  have hremRadius : ENNReal.ofNNReal ρ <
      (sigmaZeroPairRemainderSeries d (m : ℝ) ζ).radius := by
    calc
      ENNReal.ofNNReal ρ < ENNReal.ofNNReal (sNN ^ 2) := ENNReal.coe_lt_coe.mpr hρupper
      _ ≤ Q.radius := by
        simpa [sNN, ← ENNReal.coe_pow] using hQradius
      _ = (sigmaZeroPairRemainderSeries d (m : ℝ) ζ).radius := by rw [hQeq]
  have hdecompR : ∀ᶠ u : ℂ in 𝓝 0,
      completedSigmaLogJetComplexGeneratingFunction d u =
        sigmaZeroPairRationalModel (m : ℝ) ζ u +
          (sigmaZeroPairRemainderSeries d (m : ℝ) ζ).sum u := by
    filter_upwards [hdecomp] with u hu
    simpa [hQeq] using hu
  have hresult :=
    completedSigmaLogJet_zeroPair_conditional_decomposition d (m : ℝ) ζ hd₁ hd₂
      (zpow_ne_zero _ hτ) hmodel ρ hmodelRadius hremRadius hdecompR
  simpa [τ, ζ] using hresult

/-- Continuous square-root branch on the upper half-plane, written in real coordinates. -/
def sigmaUpperHalfPlaneSqrt (z : ℂ) : ℂ :=
  (Real.sqrt ((‖z‖ + z.re) / 2) : ℂ) +
    Complex.I * (Real.sqrt ((‖z‖ - z.re) / 2) : ℂ)

theorem sigmaUpperHalfPlaneSqrt_continuous : Continuous sigmaUpperHalfPlaneSqrt := by
  fun_prop [sigmaUpperHalfPlaneSqrt]

/-- The explicit upper-half-plane branch squares back to its argument. -/
theorem sigmaUpperHalfPlaneSqrt_sq (z : ℂ) (hz : 0 < z.im) :
    sigmaUpperHalfPlaneSqrt z ^ 2 = z := by
  let x : ℝ := Real.sqrt ((‖z‖ + z.re) / 2)
  let y : ℝ := Real.sqrt ((‖z‖ - z.re) / 2)
  have hnormRe : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
  have hxarg : 0 ≤ (‖z‖ + z.re) / 2 := by
    have := (abs_le.mp hnormRe).1
    linarith
  have hyarg : 0 ≤ (‖z‖ - z.re) / 2 := by
    have := (abs_le.mp hnormRe).2
    linarith
  have hx : x ^ 2 = (‖z‖ + z.re) / 2 := by
    dsimp [x]
    exact Real.sq_sqrt hxarg
  have hy' : y ^ 2 = (‖z‖ - z.re) / 2 := by
    dsimp [y]
    exact Real.sq_sqrt hyarg
  have hnorm : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    have h := Complex.normSq_eq_norm_sq z
    rw [Complex.normSq_apply] at h
    nlinarith [h]
  have hxySq : (2 * x * y) ^ 2 = z.im ^ 2 := by
    rw [show (2 * x * y) ^ 2 = 4 * (x ^ 2) * (y ^ 2) by ring, hx, hy']
    nlinarith [hnorm]
  have hxyNonneg : 0 ≤ 2 * x * y := by positivity [x, y]
  have hxy : 2 * x * y = z.im := by nlinarith [hxySq, hxyNonneg, hz]
  let w : ℂ := (x : ℂ) + Complex.I * (y : ℂ)
  have hwre : w.re = x := by simp [w]
  have hwim : w.im = y := by simp [w]
  have hS : sigmaUpperHalfPlaneSqrt z = w := by
    simp [sigmaUpperHalfPlaneSqrt, x, y, w]
  rw [hS, pow_two]
  apply Complex.ext
  · rw [Complex.mul_re, hwre, hwim]
    calc
      x * x - y * y = x ^ 2 - y ^ 2 := by ring
      _ = (‖z‖ + z.re) / 2 - (‖z‖ - z.re) / 2 := by rw [hx, hy']
      _ = z.re := by ring
  · rw [Complex.mul_im, hwre, hwim]
    calc
      x * y + y * x = 2 * x * y := by ring
      _ = z.im := hxy

/-- At a positive-height point, the explicit square-root branch selects the root
with positive real and imaginary parts. -/
theorem sigmaUpperHalfPlaneSqrt_height_sq (γ d : ℝ) (hγ : 0 < γ) (hd : 0 < d) :
    sigmaUpperHalfPlaneSqrt (((γ : ℂ) + (d : ℂ) * Complex.I) ^ 2) =
      (γ : ℂ) + (d : ℂ) * Complex.I := by
  let w : ℂ := (γ : ℂ) + (d : ℂ) * Complex.I
  have hwre : w.re = γ := by simp [w]
  have hwim : w.im = d := by simp [w]
  have hnormSq : Complex.normSq w = γ ^ 2 + d ^ 2 := by
    rw [Complex.normSq_apply]
    simp [hwre, hwim]
    ring
  have hnorm : ‖w‖ ^ 2 = γ ^ 2 + d ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    exact hnormSq
  have hnorm2 : ‖w ^ 2‖ = γ ^ 2 + d ^ 2 := by
    rw [norm_pow]
    nlinarith [norm_nonneg w]
  have hre : (w ^ 2).re = γ ^ 2 - d ^ 2 := by
    rw [pow_two, Complex.mul_re, hwre, hwim]
    ring
  have him : (w ^ 2).im = 2 * γ * d := by
    rw [pow_two, Complex.mul_im, hwre, hwim]
    ring
  have hplus : (‖w ^ 2‖ + (w ^ 2).re) / 2 = γ ^ 2 := by
    rw [hnorm2, hre]
    ring
  have hminus : (‖w ^ 2‖ - (w ^ 2).re) / 2 = d ^ 2 := by
    rw [hnorm2, hre]
    ring
  have hsqrtγ : Real.sqrt ((‖w ^ 2‖ + (w ^ 2).re) / 2) = γ := by
    rw [hplus, Real.sqrt_sq_eq_abs, abs_of_pos hγ]
  have hsqrtd : Real.sqrt ((‖w ^ 2‖ - (w ^ 2).re) / 2) = d := by
    rw [hminus, Real.sqrt_sq_eq_abs, abs_of_pos hd]
  change sigmaUpperHalfPlaneSqrt (w ^ 2) = w
  rw [sigmaUpperHalfPlaneSqrt, hsqrtγ, hsqrtd]
  calc
    (γ : ℂ) + Complex.I * (d : ℂ) = (γ : ℂ) + (d : ℂ) * Complex.I := by ring
    _ = w := by rfl

/-- The selected lower Padé root is converted to its upper-half-plane inverse-square-root
branch. -/
def sigmaPadeRecoveredHeight (d : ℝ) (k : ℕ) : ℂ :=
  sigmaUpperHalfPlaneSqrt
    (Inv.inv (sigmaPadeQuadraticRootLower (-1) (-sigmaPadeAlpha d k) (-sigmaPadeBeta d k)))

/-- The isolated source factorization and Cauchy remainder bound feed the existing two-pole
root theorem for the original sigma Padé pencil. The original pencil is retained throughout. -/
theorem completedNative_sigmaRemainder_pade_root_of_isolation
    (d γ r : ℝ) (m : ℕ)
    (hisolation : SigmaDisplacedProductIsolation d γ r m) :
    ∃ C η : ℝ, 0 < C ∧ 0 < η ∧
      η < ‖((γ : ℂ) + Complex.I * (d : ℂ)) ^ (-2 : ℤ)‖ ∧
      (∀ n, (completedSigmaLogJet d n : ℂ) =
        (twoPoleMoment (m : ℝ) (((γ : ℂ) + Complex.I * (d : ℂ)) ^ (-2 : ℤ)) n : ℂ) +
          (sigmaZeroPairRemainderMoment d (m : ℝ)
            (((γ : ℂ) + Complex.I * (d : ℂ)) ^ (-2 : ℤ)) n : ℂ)) ∧
      (∀ n, |sigmaZeroPairRemainderMoment d (m : ℝ)
        (((γ : ℂ) + Complex.I * (d : ℂ)) ^ (-2 : ℤ)) n| ≤ C * η ^ n) ∧
      Tendsto (fun k => sigmaPadeQuadraticRootLower (-1)
        (-sigmaPadeAlpha d k) (-sigmaPadeBeta d k)) atTop
          (𝓝 (((γ : ℂ) + Complex.I * (d : ℂ)) ^ (-2 : ℤ))) ∧
      Tendsto (fun k => star (sigmaPadeQuadraticRootLower (-1)
        (-sigmaPadeAlpha d k) (-sigmaPadeBeta d k))) atTop
          (𝓝 (star (((γ : ℂ) + Complex.I * (d : ℂ)) ^ (-2 : ℤ)))) ∧
      Tendsto (fun k => sigmaPadeRecoveredHeight d k) atTop
        (𝓝 ((γ : ℂ) + Complex.I * (d : ℂ))) ∧
      Tendsto (fun k => star (sigmaPadeRecoveredHeight d k)) atTop
        (𝓝 ((γ : ℂ) - Complex.I * (d : ℂ))) ∧
      ∀ᶠ k : ℕ in atTop,
        sigmaPencilCharacteristicComplex d k
          (sigmaPadeQuadraticRootLower (-1) (-sigmaPadeAlpha d k)
            (-sigmaPadeBeta d k)) = 0 ∧
        sigmaPencilCharacteristicComplex d k
          (star (sigmaPadeQuadraticRootLower (-1) (-sigmaPadeAlpha d k)
            (-sigmaPadeBeta d k))) = 0 ∧
        (sigmaPadeQuadraticRootLower (-1) (-sigmaPadeAlpha d k)
          (-sigmaPadeBeta d k)).im ≠ 0 ∧
        (sigmaPadeRecoveredHeight d k) ^ 2 =
          (sigmaPadeQuadraticRootLower (-1) (-sigmaPadeAlpha d k)
            (-sigmaPadeBeta d k))⁻¹ ∧
        (star (sigmaPadeRecoveredHeight d k)) ^ 2 = star
          ((sigmaPadeQuadraticRootLower (-1) (-sigmaPadeAlpha d k)
            (-sigmaPadeBeta d k))⁻¹) := by
  classical
  let τ : ℂ := (γ : ℂ) + Complex.I * (d : ℂ)
  let ζ : ℂ := τ ^ (-2 : ℤ)
  let R : ℝ := γ ^ 2 + d ^ 2
  let a : ℝ := R⁻¹
  let θ : ℂ := (R : ℂ) * inverseSquareNode γ d
  let x : ℝ := θ.re
  let y : ℝ := θ.im
  have hγ : 0 < γ := hisolation.height_pos
  have hd : 0 < d := hisolation.displacement_pos
  have hR : 0 < R := by dsimp [R]; positivity
  have hτnode : τ = (γ : ℂ) + (d : ℂ) * Complex.I := by
    dsimp [τ]
    ring
  have hζnode : ζ = inverseSquareNode γ d := by
    dsimp [ζ]
    rw [hτnode]
    simp [inverseSquareNode, zpow_neg, inv_pow]
    rfl
  have hθunit : Complex.normSq θ = 1 := by
    change Complex.normSq ((R : ℂ) * inverseSquareNode γ d) = 1
    rw [Complex.normSq_mul, Complex.normSq_ofReal,
      inverseSquareNode_normSq γ d hγ]
    dsimp [R]
    field_simp
  have hθim : θ.im = -(2 * γ * d) / R := by
    change ((R : ℂ) * inverseSquareNode γ d).im = _
    rw [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re]
    simp only [zero_mul, add_zero]
    rw [inverseSquareNode_im γ d hγ]
    dsimp [R]
    field_simp [ne_of_gt hR]
  have hy : y < 0 := by
    dsimp [y]
    rw [hθim]
    have hnum : 0 < 2 * γ * d := by positivity
    exact div_neg_of_neg_of_pos (neg_neg_of_pos hnum) hR
  have ha : 0 < a := by dsimp [a]; exact inv_pos.mpr hR
  have hζfactor : ζ = (a : ℂ) * θ := by
    have haR : a * R = 1 := by dsimp [a]; field_simp [ne_of_gt hR]
    calc
      ζ = (1 : ℂ) * inverseSquareNode γ d := by rw [hζnode]; simp
      _ = ((a * R : ℝ) : ℂ) * inverseSquareNode γ d := by rw [haR]; simp
      _ = (a : ℂ) * ((R : ℂ) * inverseSquareNode γ d) := by push_cast; ring
  have hre : θ.re = x := rfl
  have him : θ.im = y := rfl
  have hnormθsq : ‖θ‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq θ]
    exact hθunit
  have hnormθ : ‖θ‖ = 1 := by
    have hnonneg := norm_nonneg θ
    nlinarith
  have hnormζ : ‖ζ‖ = a := by
    rw [hζfactor, norm_mul, hnormθ]
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
  obtain ⟨C, η, hC, hη, hηζ, hcoeff, hbound⟩ :=
    completedNative_sigmaRemainder_square_decomposition_of_isolation
      d γ r m hisolation
  have hηa : η < a := by
    have hηζ' : η < ‖ζ‖ := by simpa [ζ, τ] using hηζ
    rw [← hnormζ]
    exact hηζ'
  have hroot := sigmaPadeOriginalPencil_root_tendsto_to_twoPole
    d (m : ℝ) a C η x y ζ θ hζfactor hre him hθunit (le_of_lt hη) ha hηa
      (Nat.cast_ne_zero.mpr hisolation.multiplicity_pos.ne') hy hbound
  let root : ℕ → ℂ := fun k =>
    sigmaPadeQuadraticRootLower (-1) (-sigmaPadeAlpha d k) (-sigmaPadeBeta d k)
  have hrootlim : Tendsto root atTop (𝓝 ζ) := by simpa [root] using hroot.1
  have hrootConjlim : Tendsto (fun k => star (root k)) atTop (𝓝 (star ζ)) := by
    have hcont := Complex.continuous_conj.continuousAt.tendsto.comp hrootlim
    change Tendsto (fun k => star (root k)) atTop (𝓝 (star ζ))
    exact hcont
  have hτ : τ ≠ 0 := by
    intro hzero
    have hreτ : τ.re = 0 := by rw [hzero]; simp
    simp [τ] at hreτ
    linarith
  have hζne : ζ ≠ 0 := zpow_ne_zero _ hτ
  have hζinv : ζ⁻¹ = τ ^ 2 := by
    rw [hζnode]
    simp [inverseSquareNode, inv_pow, hτnode]
  have hrootInv0 : Tendsto (fun k => (root k)⁻¹) atTop (𝓝 (ζ⁻¹)) :=
    hrootlim.inv₀ hζne
  have hrootInv : Tendsto (fun k => (root k)⁻¹) atTop (𝓝 (τ ^ 2)) := by
    simpa [hζinv] using hrootInv0
  have hτsqIm : 0 < (τ ^ 2).im := by
    rw [hτnode]
    simp [pow_two, Complex.mul_im]
    positivity
  have hbranch : sigmaUpperHalfPlaneSqrt (τ ^ 2) = τ := by
    rw [hτnode]
    exact sigmaUpperHalfPlaneSqrt_height_sq γ d hγ hd
  have hheight : Tendsto (fun k => sigmaPadeRecoveredHeight d k) atTop (𝓝 τ) := by
    have hcont := sigmaUpperHalfPlaneSqrt_continuous.continuousAt.tendsto.comp hrootInv
    change Tendsto (sigmaUpperHalfPlaneSqrt ∘ (fun k => Inv.inv (root k))) atTop (𝓝 τ)
    simpa only [hbranch] using hcont
  have hstarτ : star τ = (γ : ℂ) - Complex.I * (d : ℂ) := by
    rw [hτnode]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  have hheightConj : Tendsto (fun k => star (sigmaPadeRecoveredHeight d k)) atTop
      (𝓝 ((γ : ℂ) - Complex.I * (d : ℂ))) := by
    have hcont := Complex.continuous_conj.continuousAt.tendsto.comp hheight
    have hcont' := hcont
    change Tendsto (fun k => star (sigmaPadeRecoveredHeight d k)) atTop
      (𝓝 (star τ)) at hcont'
    simpa only [hstarτ] using hcont'
  have hImTendsto : Tendsto (fun k => ((root k)⁻¹).im) atTop (𝓝 (τ ^ 2).im) :=
    Complex.continuous_im.continuousAt.tendsto.comp hrootInv
  have hImEvent : ∀ᶠ k : ℕ in atTop, 0 < ((root k)⁻¹).im :=
    hImTendsto.eventually (Ioi_mem_nhds hτsqIm)
  have hheightSq : ∀ᶠ k : ℕ in atTop, (sigmaPadeRecoveredHeight d k) ^ 2 = (root k)⁻¹ := by
    filter_upwards [hImEvent] with k hk
    simpa [sigmaPadeRecoveredHeight, root, Inv.inv] using
      sigmaUpperHalfPlaneSqrt_sq ((root k)⁻¹) hk
  have hheightConjSq : ∀ᶠ k : ℕ in atTop,
      (star (sigmaPadeRecoveredHeight d k)) ^ 2 = star ((root k)⁻¹) := by
    filter_upwards [hheightSq] with k hk
    calc
      (star (sigmaPadeRecoveredHeight d k)) ^ 2 =
          star ((sigmaPadeRecoveredHeight d k) ^ 2) := by simp
      _ = star ((root k)⁻¹) := by rw [hk]
  have hconjrootEvent : ∀ᶠ k : ℕ in atTop,
      sigmaPencilCharacteristicComplex d k (star (root k)) = 0 := by
    filter_upwards [hroot.2] with k hk
    have hpoly : (sigmaPadeD d k : ℂ) * (root k) ^ 2 -
        (sigmaPadeB d k : ℂ) * root k + (sigmaPadeC d k : ℂ) = 0 := by
      simpa [sigmaPencilCharacteristicComplex_eq_quadratic] using hk.1
    have hstar := congrArg star hpoly
    have hstarPoly : (sigmaPadeD d k : ℂ) * star (root k) ^ 2 -
        (sigmaPadeB d k : ℂ) * star (root k) + (sigmaPadeC d k : ℂ) = 0 := by
      simpa using hstar
    simpa [sigmaPencilCharacteristicComplex_eq_quadratic] using hstarPoly
  have hfinalEvent : ∀ᶠ k : ℕ in atTop,
      sigmaPencilCharacteristicComplex d k (root k) = 0 ∧
      sigmaPencilCharacteristicComplex d k (star (root k)) = 0 ∧
      (root k).im ≠ 0 ∧
      (sigmaPadeRecoveredHeight d k) ^ 2 = (root k)⁻¹ ∧
      (star (sigmaPadeRecoveredHeight d k)) ^ 2 = star ((root k)⁻¹) := by
    filter_upwards [hroot.2, hconjrootEvent, hheightSq, hheightConjSq]
      with k hk hconj hsq hcsq
    exact ⟨hk.1, hconj, hk.2, hsq, hcsq⟩
  simpa [τ, ζ] using
    (show ∃ C η : ℝ, 0 < C ∧ 0 < η ∧
      η < ‖ζ‖ ∧
      (∀ n, (completedSigmaLogJet d n : ℂ) =
        (twoPoleMoment (m : ℝ) ζ n : ℂ) +
          (sigmaZeroPairRemainderMoment d (m : ℝ) ζ n : ℂ)) ∧
      (∀ n, |sigmaZeroPairRemainderMoment d (m : ℝ) ζ n| ≤ C * η ^ n) ∧
      Tendsto (fun k => sigmaPadeQuadraticRootLower (-1)
        (-sigmaPadeAlpha d k) (-sigmaPadeBeta d k)) atTop (𝓝 ζ) ∧
      Tendsto (fun k => star (sigmaPadeQuadraticRootLower (-1)
        (-sigmaPadeAlpha d k) (-sigmaPadeBeta d k))) atTop (𝓝 (star ζ)) ∧
      Tendsto (fun k => sigmaPadeRecoveredHeight d k) atTop (𝓝 τ) ∧
      Tendsto (fun k => star (sigmaPadeRecoveredHeight d k)) atTop
        (𝓝 ((γ : ℂ) - Complex.I * (d : ℂ))) ∧
      ∀ᶠ k : ℕ in atTop,
        sigmaPencilCharacteristicComplex d k
          (sigmaPadeQuadraticRootLower (-1) (-sigmaPadeAlpha d k)
            (-sigmaPadeBeta d k)) = 0 ∧
        sigmaPencilCharacteristicComplex d k
          (star (sigmaPadeQuadraticRootLower (-1) (-sigmaPadeAlpha d k)
            (-sigmaPadeBeta d k))) = 0 ∧
        (sigmaPadeQuadraticRootLower (-1) (-sigmaPadeAlpha d k)
          (-sigmaPadeBeta d k)).im ≠ 0 ∧
        (sigmaPadeRecoveredHeight d k) ^ 2 =
          (sigmaPadeQuadraticRootLower (-1) (-sigmaPadeAlpha d k)
            (-sigmaPadeBeta d k))⁻¹ ∧
        (star (sigmaPadeRecoveredHeight d k)) ^ 2 =
          (star (sigmaPadeQuadraticRootLower (-1) (-sigmaPadeAlpha d k)
            (-sigmaPadeBeta d k)))⁻¹ from
      ⟨C, η, hC, hη, hηζ, hcoeff, hbound, hrootlim, hrootConjlim, hheight, hheightConj,
        by simpa [root, star_inv₀] using hfinalEvent⟩)

/-! ## Axiom audit -/

#print axioms CarrySigmaObstruction.analytic_even_taylor_series_sum
#print axioms CarrySigmaObstruction.analytic_even_taylor_series_radius
#print axioms CarrySigmaObstruction.analytic_even_has_square_series
#print axioms CarrySigmaObstruction.analytic_eventually_zero_of_comp_square
#print axioms CarrySigmaObstruction.twoPoleMoment_complex_eq
#print axioms CarrySigmaObstruction.sigmaZeroPairRationalModel_hasFPowerSeriesAt
#print axioms CarrySigmaObstruction.sigmaTwoPoleFactor_logDerivative
#print axioms CarrySigmaObstruction.sigmaDisplacedFirstPoleFactor_eq_twoPoleFactor
#print axioms CarrySigmaObstruction.neg_deriv_mul_div_eq_add
#print axioms CarrySigmaObstruction.sigmaDisplacedFirstPoleFactor_logDerivative
#print axioms CarrySigmaObstruction.completedNative_sigmaRemainder_local_of_isolation
#print axioms CarrySigmaObstruction.completedNative_sigmaRemainder_square_decomposition_of_isolation
#print axioms CarrySigmaObstruction.completedNative_sigmaRemainder_pade_root_of_isolation

end
end CarrySigmaObstruction
