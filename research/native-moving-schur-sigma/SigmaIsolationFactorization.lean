import SigmaNativeContinuation
import Mathlib.Analysis.Analytic.Order

/-!
# Analytic quotient from an isolated zero set

This module contains the non-circular analytic division step needed for the pole isolation
argument. It starts from an explicit zero-set predicate and exact local orders for the source and
the proposed pole factor. It constructs the quotient, proves it analytic across the removed
zeros, and proves it nonvanishing. No quotient factor is supplied as part of the certificate.
-/

namespace CarrySigmaObstruction

open Filter Topology

noncomputable section
set_option autoImplicit false

/-- The derivative at the center of an analytic even function vanishes. -/
lemma analyticAt_deriv_eq_zero_of_even (f : ℂ → ℂ)
    (hf : AnalyticAt ℂ f 0)
    (heven : ∀ᶠ z : ℂ in 𝓝 0, f (-z) = f z) : deriv f 0 = 0 := by
  have heq : (fun z : ℂ => f (-z)) =ᶠ[𝓝 0] f := heven
  have hderivEq : deriv (fun z : ℂ => f (-z)) 0 = deriv f 0 :=
    heq.deriv.self_of_nhds
  have hfderiv : HasDerivAt f (deriv f 0) 0 := hf.differentiableAt.hasDerivAt
  have hfderiv' : HasDerivAt f (deriv f 0) (-0) := by simpa using hfderiv
  have hcomp : HasDerivAt (fun z : ℂ => f (-z)) (-(deriv f 0)) 0 := by
    simpa [Function.comp_def] using
      HasDerivAt.comp (x := (0 : ℂ)) hfderiv' (hasDerivAt_neg (0 : ℂ))
  have hneg : deriv (fun z : ℂ => f (-z)) 0 = -(deriv f 0) := hcomp.deriv
  have hmain : deriv f 0 = -(deriv f 0) := hderivEq.symm.trans hneg
  have hsum : deriv f 0 + deriv f 0 = 0 := by
    calc
      deriv f 0 + deriv f 0 = deriv f 0 + -(deriv f 0) :=
        congrArg (fun y : ℂ => deriv f 0 + y) hmain
      _ = 0 := by simp
  have hmul : (2 : ℂ) * deriv f 0 = 0 := by simpa [two_mul] using hsum
  exact (mul_eq_zero.mp hmul).resolve_left (by norm_num)

/-- Analytic division by the centered coordinate: an analytic function vanishing at zero is
locally `z` times another analytic function. The infinite-order case is handled by local
vanishing; the finite-order case factors the exact analytic order and lowers it by one. -/
lemma analyticAt_factor_by_id_of_zero (f : ℂ → ℂ)
    (hf : AnalyticAt ℂ f 0) (hzero : f 0 = 0) :
    ∃ q : ℂ → ℂ, AnalyticAt ℂ q 0 ∧ ∀ᶠ z : ℂ in 𝓝 0, f z = z * q z := by
  by_cases htop : analyticOrderAt f 0 = ⊤
  · refine ⟨0, analyticAt_const, ?_⟩
    filter_upwards [(analyticOrderAt_eq_top).mp htop] with z hz
    simp [hz]
  · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp htop
    have hmpos : 0 < m := by
      by_contra hmnot
      have hmzero : m = 0 := Nat.eq_zero_of_not_pos hmnot
      subst m
      apply (hf.analyticOrderAt_ne_zero.mpr hzero)
      simpa using hm.symm
    have horder : analyticOrderAt f 0 = m := hm.symm
    obtain ⟨g, hg, hg0, hfactor⟩ := (hf.analyticOrderAt_eq_natCast).mp horder
    let q : ℂ → ℂ := fun z => z ^ (m - 1) * g z
    have hq : AnalyticAt ℂ q 0 := by
      dsimp [q]
      exact (analyticAt_id.pow (m - 1)).mul hg
    have hm' : m - 1 + 1 = m := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hmpos.ne')
    refine ⟨q, hq, ?_⟩
    filter_upwards [hfactor] with z hz
    have hfac : f z = z ^ m * g z := by
      simpa [smul_eq_mul] using hz
    rw [hfac]
    dsimp [q]
    calc
      z ^ m * g z = z ^ (m - 1 + 1) * g z := by rw [hm']
      _ = (z ^ (m - 1) * z) * g z := by rw [pow_succ]
      _ = z * (z ^ (m - 1) * g z) := by ring

/-- The logarithmic derivative divided by the centered variable has a genuine analytic removal
at zero whenever the derivative has been analytically divided by that coordinate. -/
lemma analyticLogDerivative_div_t_analyticAt_zero
    (H q : ℂ → ℂ) (hH : AnalyticAt ℂ H 0) (hH0 : H 0 ≠ 0)
    (hq : AnalyticAt ℂ q 0)
    (hfactor : ∀ᶠ z : ℂ in 𝓝 0, deriv H z = z * q z) :
    AnalyticAt ℂ (fun z : ℂ =>
      if z = 0 then -q z / (4 * H z) else -deriv H z / (4 * z * H z)) 0 := by
  have hden : AnalyticAt ℂ (fun z : ℂ => 4 * H z) 0 :=
    analyticAt_const.mul hH
  have hden0 : 4 * H 0 ≠ 0 := mul_ne_zero (by norm_num) hH0
  have hregular : AnalyticAt ℂ (fun z : ℂ => -q z / (4 * H z)) 0 := by
    exact hq.neg.div hden hden0
  have hHne : ∀ᶠ z : ℂ in 𝓝 0, H z ≠ 0 := hH.continuousAt.eventually_ne hH0
  have hnear : (fun z : ℂ =>
      if z = 0 then -q z / (4 * H z) else -deriv H z / (4 * z * H z)) =ᶠ[𝓝 0]
      (fun z : ℂ => -q z / (4 * H z)) := by
    filter_upwards [hfactor, hHne] with z hfac hHz
    by_cases hz : z = 0
    · subst z
      simp
    · simp only [if_neg hz]
      rw [hfac]
      field_simp [hz, hHz]
  exact hregular.congr hnear.symm

/-- The logarithmic derivative remainder in the displacement variable, with its removable value
at the center supplied by the analytic quotient `q`. -/
def sigmaDisplacedLogRemainderT (H q : ℂ → ℂ) (z : ℂ) : ℂ :=
  if z = 0 then -q z / (4 * H z) else -deriv H z / (4 * z * H z)

/-- The regularized logarithmic derivative of an analytic, nowhere-zero `H` is analytic on its
whole disk. Only the center uses the local analytic division certificate; away from zero this is
ordinary analytic division. -/
theorem sigmaDisplacedLogRemainderT_analyticOnNhd
    (r : ℝ) (hr : 0 < r) (H q : ℂ → ℂ)
    (hH : ∀ z ∈ Metric.ball 0 r, AnalyticAt ℂ H z)
    (hHne : ∀ z ∈ Metric.ball 0 r, H z ≠ 0)
    (hq : AnalyticAt ℂ q 0)
    (hfactor : ∀ᶠ z : ℂ in 𝓝 0, deriv H z = z * q z) :
    AnalyticOnNhd ℂ (sigmaDisplacedLogRemainderT H q) (Metric.ball 0 r) := by
  intro z hz
  by_cases hz0 : z = 0
  · subst z
    exact analyticLogDerivative_div_t_analyticAt_zero H q
      (hH 0 (Metric.mem_ball_self hr)) (hHne 0 (Metric.mem_ball_self hr)) hq hfactor
  · have hden : AnalyticAt ℂ (fun w : ℂ => 4 * w * H w) z := by
      fun_prop
    have hden0 : 4 * z * H z ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) hz0) (hHne z hz)
    have hregular : AnalyticAt ℂ
        (fun w : ℂ => -deriv H w / (4 * w * H w)) z :=
      ((hH z hz).deriv).neg.div hden hden0
    have hnear : sigmaDisplacedLogRemainderT H q =ᶠ[𝓝 z]
        (fun w : ℂ => -deriv H w / (4 * w * H w)) := by
      filter_upwards [continuousAt_id.eventually_ne hz0] with w hw
      have hw0 : w ≠ 0 := by simpa using hw
      simp [sigmaDisplacedLogRemainderT, hw0]
    exact hregular.congr hnear.symm

/-- The derivative of an even analytic function is odd at every point of its symmetric disk. -/
lemma analyticOnNhd_even_deriv_neg
    (r : ℝ) (H : ℂ → ℂ)
    (hH : ∀ z ∈ Metric.ball 0 r, AnalyticAt ℂ H z)
    (hHeven : ∀ z ∈ Metric.ball 0 r, H (-z) = H z)
    (z : ℂ) (hz : z ∈ Metric.ball 0 r) :
    deriv H (-z) = -deriv H z := by
  have hzR : ‖z‖ < r := by
    simpa [Metric.mem_ball, dist_eq_norm] using hz
  have hnegR : ‖-z‖ < r := by simpa [norm_neg] using hzR
  have hnegU : -z ∈ Metric.ball 0 r := by
    simpa [Metric.mem_ball, dist_eq_norm] using hnegR
  have hballOpen : IsOpen (Metric.ball (0 : ℂ) r) := Metric.isOpen_ball
  have hUevent : ∀ᶠ w : ℂ in 𝓝 z, w ∈ Metric.ball 0 r := hballOpen.mem_nhds hz
  have hEvenEvent : ∀ᶠ w : ℂ in 𝓝 z, H (-w) = H w := by
    filter_upwards [hUevent] with w hw
    exact hHeven w hw
  have hEq : (fun w : ℂ => H (-w)) =ᶠ[𝓝 z] H := hEvenEvent
  have hderivEq : deriv (fun w : ℂ => H (-w)) z = deriv H z :=
    hEq.deriv.self_of_nhds
  have hHderiv : HasDerivAt H (deriv H (-z)) (-z) :=
    (hH (-z) hnegU).differentiableAt.hasDerivAt
  have hcomp : HasDerivAt (fun w : ℂ => H (-w)) (-deriv H (-z)) z := by
    simpa [Function.comp_def] using
      HasDerivAt.comp (x := z) hHderiv (hasDerivAt_neg z)
  have hmain : deriv H z = -deriv H (-z) := hderivEq.symm.trans hcomp.deriv
  have hneg := congrArg Neg.neg hmain
  simpa using hneg.symm

/-- Evenness of `H` makes the regularized logarithmic derivative an even function of `t`. -/
theorem sigmaDisplacedLogRemainderT_even
    (r : ℝ) (H q : ℂ → ℂ)
    (hH : ∀ z ∈ Metric.ball 0 r, AnalyticAt ℂ H z)
    (hHne : ∀ z ∈ Metric.ball 0 r, H z ≠ 0)
    (hHeven : ∀ z ∈ Metric.ball 0 r, H (-z) = H z)
    (z : ℂ) (hz : z ∈ Metric.ball 0 r) :
    sigmaDisplacedLogRemainderT H q (-z) = sigmaDisplacedLogRemainderT H q z := by
  by_cases hz0 : z = 0
  · subst z
    simp [sigmaDisplacedLogRemainderT]
  · have hzR : ‖z‖ < r := by
      simpa [Metric.mem_ball, dist_eq_norm] using hz
    have hnegR : ‖-z‖ < r := by simpa [norm_neg] using hzR
    have hnegU : -z ∈ Metric.ball 0 r := by
      simpa [Metric.mem_ball, dist_eq_norm] using hnegR
    have hderiv := analyticOnNhd_even_deriv_neg r H hH hHeven z hz
    have hneg0 : -z ≠ 0 := by simpa using hz0
    simp only [sigmaDisplacedLogRemainderT, if_neg hz0, if_neg hneg0]
    rw [hHeven z hz, hderiv]
    field_simp [hz0, hneg0, hHne z hz]

/-- If two analytic functions have exactly the same isolated zeros, with the same positive
order at each zero, their quotient extends to an analytic nowhere-zero function. The proof
constructs the values at the removed points from their local analytic factors. -/
theorem analyticQuotientExtension_of_isolated_zeros
    (U : Set ℂ) (hU : IsOpen U) (f p : ℂ → ℂ) (m : ℕ)
    (hf : ∀ z ∈ U, AnalyticAt ℂ f z)
    (hp : ∀ z ∈ U, AnalyticAt ℂ p z)
    (hzeros : ∀ z ∈ U, f z = 0 ↔ p z = 0)
    (horders : ∀ z ∈ U, p z = 0 →
      analyticOrderAt f z = m ∧ analyticOrderAt p z = m)
    (hisolated : ∀ z ∈ U, p z = 0 →
      ∀ᶠ w : ℂ in 𝓝 z, p w = 0 → w = z) :
    ∃ H : ℂ → ℂ,
      (∀ z ∈ U, AnalyticAt ℂ H z) ∧
      (∀ z ∈ U, f z = p z * H z) ∧
      (∀ z ∈ U, H z ≠ 0) := by
  classical
  have hlocalExists (z : ℂ) (hz : z ∈ U) (hpz : p z = 0) :
      ∃ q : (ℂ → ℂ) × (ℂ → ℂ),
        AnalyticAt ℂ q.1 z ∧ q.1 z ≠ 0 ∧
          (∀ᶠ w : ℂ in 𝓝 z, f w = (w - z) ^ m * q.1 w) ∧
        AnalyticAt ℂ q.2 z ∧ q.2 z ≠ 0 ∧
          (∀ᶠ w : ℂ in 𝓝 z, p w = (w - z) ^ m * q.2 w) := by
    obtain ⟨qf, hqf, hqf0, hfqf⟩ :=
      (hf z hz).analyticOrderAt_eq_natCast.mp (horders z hz hpz).1
    obtain ⟨qp, hqp, hqp0, hpqp⟩ :=
      (hp z hz).analyticOrderAt_eq_natCast.mp (horders z hz hpz).2
    exact ⟨(qf, qp), hqf, hqf0, by simpa [smul_eq_mul] using hfqf,
      hqp, hqp0, by simpa [smul_eq_mul] using hpqp⟩
  let localFactors : ∀ z : ℂ, ∀ hz : z ∈ U, ∀ hpz : p z = 0,
      (ℂ → ℂ) × (ℂ → ℂ) := fun z hz hpz =>
    Classical.choose (hlocalExists z hz hpz)
  have localFactors_spec (z : ℂ) (hz : z ∈ U) (hpz : p z = 0) :
      AnalyticAt ℂ (localFactors z hz hpz).1 z ∧
        (localFactors z hz hpz).1 z ≠ 0 ∧
          (∀ᶠ w : ℂ in 𝓝 z,
            f w = (w - z) ^ m * (localFactors z hz hpz).1 w) ∧
        AnalyticAt ℂ (localFactors z hz hpz).2 z ∧
        (localFactors z hz hpz).2 z ≠ 0 ∧
          (∀ᶠ w : ℂ in 𝓝 z,
            p w = (w - z) ^ m * (localFactors z hz hpz).2 w) :=
    Classical.choose_spec (hlocalExists z hz hpz)
  let H : ℂ → ℂ := fun z =>
    if hz : z ∈ U then
      if hpz : p z = 0 then
        (localFactors z hz hpz).1 z / (localFactors z hz hpz).2 z
      else f z / p z
    else 0
  have hHanalytic : ∀ z ∈ U, AnalyticAt ℂ H z := by
    intro z hz
    by_cases hpz : p z = 0
    · let qf := (localFactors z hz hpz).1
      let qp := (localFactors z hz hpz).2
      have hspec := localFactors_spec z hz hpz
      have hqf : AnalyticAt ℂ qf z := by simpa [qf] using hspec.1
      have hqf0 : qf z ≠ 0 := by simpa [qf] using hspec.2.1
      have hqfeq : ∀ᶠ w : ℂ in 𝓝 z, f w = (w - z) ^ m * qf w := by
        simpa [qf] using hspec.2.2.1
      have hqp : AnalyticAt ℂ qp z := by simpa [qp] using hspec.2.2.2.1
      have hqp0 : qp z ≠ 0 := by simpa [qp] using hspec.2.2.2.2.1
      have hqpeq : ∀ᶠ w : ℂ in 𝓝 z, p w = (w - z) ^ m * qp w := by
        simpa [qp] using hspec.2.2.2.2.2
      have hq : AnalyticAt ℂ (fun w : ℂ => qf w / qp w) z :=
        hqf.div hqp hqp0
      have hqpNonzero : ∀ᶠ w : ℂ in 𝓝 z, qp w ≠ 0 :=
        hqp.continuousAt.eventually_ne hqp0
      have hUevent : ∀ᶠ w : ℂ in 𝓝 z, w ∈ U :=
        hU.mem_nhds hz
      have hnear : H =ᶠ[𝓝 z] (fun w : ℂ => qf w / qp w) := by
        filter_upwards [hUevent, hisolated z hz hpz, hqfeq, hqpeq,
          hqpNonzero] with w hwU hwIso hwf hwp hwqp
        by_cases hpw : p w = 0
        · have hwz : w = z := hwIso hpw
          subst w
          simp [H, hz, hpz, qf, qp]
        · have hwz : w ≠ z := by
            intro hwz
            subst w
            exact hpw hpz
          have hpow : (w - z) ^ m ≠ 0 :=
            pow_ne_zero m (sub_ne_zero.mpr hwz)
          simp only [H, dif_pos hwU, dif_neg hpw]
          rw [hwf]
          calc
            (w - z) ^ m * qf w / p w =
                (w - z) ^ m * qf w / ((w - z) ^ m * qp w) := by rw [hwp]
            _ = qf w / qp w := by
              field_simp [hpow, hwqp]
      exact hq.congr hnear.symm
    · have hpNonzero : ∀ᶠ w : ℂ in 𝓝 z, p w ≠ 0 :=
        (hp z hz).continuousAt.eventually_ne hpz
      have hnear : H =ᶠ[𝓝 z] (fun w : ℂ => f w / p w) := by
        filter_upwards [hU.mem_nhds hz, hpNonzero] with w hwU hwp
        simp [H, hwU, hwp]
      exact (hf z hz).div (hp z hz) hpz |>.congr hnear.symm
  have hHfactor : ∀ z ∈ U, f z = p z * H z := by
    intro z hz
    by_cases hpz : p z = 0
    · have hfz : f z = 0 := (hzeros z hz).mpr hpz
      simp [hfz, hpz]
    · simp [H, hz, hpz, mul_div_cancel₀ (f z) hpz]
  have hHnonzero : ∀ z ∈ U, H z ≠ 0 := by
    intro z hz
    by_cases hpz : p z = 0
    · have hspec := localFactors_spec z hz hpz
      have hqf0 := hspec.2.1
      have hqp0 := hspec.2.2.2.2.1
      simpa [H, hz, hpz] using div_ne_zero hqf0 hqp0
    · have hfz : f z ≠ 0 := by
        intro hfz
        exact hpz ((hzeros z hz).mp hfz)
      simpa [H, hz, hpz] using div_ne_zero hfz hpz
  exact ⟨H, hHanalytic, hHfactor, hHnonzero⟩

/-- The four geometric points removed from the even displaced product. -/
def sigmaDisplacedFirstPoleRoot (τ z : ℂ) : Prop :=
  z = τ ∨ z = -τ ∨ z = star τ ∨ z = -(star τ)

/-- The normalized even factor corresponding to the first conjugate pole pair. -/
def sigmaDisplacedFirstPoleFactor (τ : ℂ) (m : ℕ) (u : ℂ) : ℂ :=
  ((fun w : ℂ => 1 - w ^ 2 / τ ^ 2) ^ m) u *
    ((fun w : ℂ => 1 - w ^ 2 / (star τ) ^ 2) ^ m) u

/-- The elementary quadratic factor vanishes exactly at its two signed roots. -/
lemma oneMinusSquareDiv_zero_iff {a z : ℂ} (ha : a ≠ 0) :
    1 - z ^ 2 / a ^ 2 = 0 ↔ z = a ∨ z = -a := by
  constructor
  · intro hz
    have hdiv : z ^ 2 / a ^ 2 = 1 := (sub_eq_zero.mp hz).symm
    have hsq : z ^ 2 = a ^ 2 := by
      have h := (div_eq_iff (pow_ne_zero 2 ha)).mp hdiv
      simpa using h
    exact eq_or_eq_neg_of_sq_eq_sq z a hsq
  · rintro (rfl | hneg)
    · simp [ha]
    · subst z
      simp [ha]

lemma oneMinusSquareDiv_ne_zero_of_not_roots {a z : ℂ} (ha : a ≠ 0)
    (hza : z ≠ a) (hzan : z ≠ -a) : 1 - z ^ 2 / a ^ 2 ≠ 0 := by
  intro hz
  rcases (oneMinusSquareDiv_zero_iff ha).mp hz with h | h
  · exact hza h
  · exact hzan h

/-- Each nonzero root of the elementary quadratic factor is simple. -/
lemma oneMinusSquareDiv_order_one {a z : ℂ} (ha : a ≠ 0)
    (hz : z = a ∨ z = -a) :
    analyticOrderAt (fun w : ℂ => 1 - w ^ 2 / a ^ 2) z = 1 := by
  have hf : AnalyticAt ℂ (fun w : ℂ => 1 - w ^ 2 / a ^ 2) z := by fun_prop
  have hzero : 1 - z ^ 2 / a ^ 2 = 0 := (oneMinusSquareDiv_zero_iff ha).2 hz
  have hz0 : z ≠ 0 := by
    rcases hz with h | h
    · simpa [h] using ha
    · intro h0
      apply ha
      exact neg_eq_zero.mp (h.symm.trans h0)
  have hderiv : deriv (fun w : ℂ => 1 - w ^ 2 / a ^ 2) z = -(2 * z / a ^ 2) := by
    rw [deriv_const_sub, deriv_div_const]
    simp
  have hderiv0 : deriv (fun w : ℂ => 1 - w ^ 2 / a ^ 2) z ≠ 0 := by
    rw [hderiv]
    exact neg_ne_zero.mpr (div_ne_zero (mul_ne_zero (by norm_num) hz0)
      (pow_ne_zero 2 ha))
  exact hf.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hzero hderiv0

/-- Under distinct signed conjugate roots, the explicit factor has exact order `m` at each of
its four roots. -/
lemma sigmaDisplacedFirstPoleFactor_order
    (τ : ℂ) (m : ℕ) (hτ : τ ≠ 0)
    (hτstar : τ ≠ star τ) (hτnegstar : τ ≠ -(star τ)) (z : ℂ)
    (hz : sigmaDisplacedFirstPoleRoot τ z) :
    analyticOrderAt (sigmaDisplacedFirstPoleFactor τ m) z = m := by
  have hstar : star τ ≠ 0 := by simpa using hτ
  have hstarτ : star τ ≠ τ := Ne.symm hτstar
  have hstarnegτ : star τ ≠ -τ := by
    intro h
    apply hτnegstar
    have := congrArg Neg.neg h
    simpa using this.symm
  have hnegτstar : -τ ≠ star τ := by
    intro h
    apply hτnegstar
    have := congrArg Neg.neg h
    simpa using this
  have hnegτnegstar : -τ ≠ -(star τ) := by
    intro h
    apply hτstar
    have := congrArg Neg.neg h
    simpa using this
  have hnegstarτ : -(star τ) ≠ τ := by
    intro h
    apply hτnegstar
    simpa [eq_comm] using h
  have hnegstarnegτ : -(star τ) ≠ -τ := by
    intro h
    apply hτstar
    have := congrArg Neg.neg h
    simpa [eq_comm] using this
  have hAanalytic (z : ℂ) : AnalyticAt ℂ (fun w : ℂ => 1 - w ^ 2 / τ ^ 2) z := by
    fun_prop
  have hBanalytic (z : ℂ) : AnalyticAt ℂ (fun w : ℂ => 1 - w ^ 2 / (star τ) ^ 2) z := by
    fun_prop
  have hprod (z : ℂ) : analyticOrderAt (sigmaDisplacedFirstPoleFactor τ m) z =
      analyticOrderAt ((fun w : ℂ => 1 - w ^ 2 / τ ^ 2) ^ m) z +
        analyticOrderAt ((fun w : ℂ => 1 - w ^ 2 / (star τ) ^ 2) ^ m) z := by
    change analyticOrderAt
        (((fun w : ℂ => 1 - w ^ 2 / τ ^ 2) ^ m) *
          ((fun w : ℂ => 1 - w ^ 2 / (star τ) ^ 2) ^ m)) z = _
    rw [analyticOrderAt_mul ((hAanalytic z).pow m) ((hBanalytic z).pow m)]
  rcases hz with hz | hz | hz | hz
  · subst z
    have hA := oneMinusSquareDiv_order_one hτ (Or.inl rfl)
    have hBne : 1 - τ ^ 2 / (star τ) ^ 2 ≠ 0 :=
      oneMinusSquareDiv_ne_zero_of_not_roots hstar hτstar hτnegstar
    have hB := (hBanalytic τ).analyticOrderAt_eq_zero.mpr hBne
    have hApow : analyticOrderAt ((fun w : ℂ => 1 - w ^ 2 / τ ^ 2) ^ m) τ = m := by
      rw [analyticOrderAt_pow (hAanalytic τ) m, hA]
      simp
    have hBpow : analyticOrderAt ((fun w : ℂ => 1 - w ^ 2 / (star τ) ^ 2) ^ m) τ = 0 := by
      rw [analyticOrderAt_pow (hBanalytic τ) m, hB]
      simp
    rw [hprod, hApow, hBpow]
    simp

  · subst z
    have hA := oneMinusSquareDiv_order_one hτ (Or.inr rfl)
    have hBne : 1 - (-τ) ^ 2 / (star τ) ^ 2 ≠ 0 :=
      oneMinusSquareDiv_ne_zero_of_not_roots hstar hnegτstar hnegτnegstar
    have hB := (hBanalytic (-τ)).analyticOrderAt_eq_zero.mpr hBne
    have hApow : analyticOrderAt ((fun w : ℂ => 1 - w ^ 2 / τ ^ 2) ^ m) (-τ) = m := by
      rw [analyticOrderAt_pow (hAanalytic (-τ)) m, hA]
      simp
    have hBpow : analyticOrderAt ((fun w : ℂ => 1 - w ^ 2 / (star τ) ^ 2) ^ m) (-τ) = 0 := by
      rw [analyticOrderAt_pow (hBanalytic (-τ)) m, hB]
      simp
    rw [hprod, hApow, hBpow]
    simp

  · subst z
    have hAne : 1 - (star τ) ^ 2 / τ ^ 2 ≠ 0 :=
      oneMinusSquareDiv_ne_zero_of_not_roots hτ hstarτ hstarnegτ
    have hA := (hAanalytic (star τ)).analyticOrderAt_eq_zero.mpr hAne
    have hB := oneMinusSquareDiv_order_one hstar (Or.inl rfl)
    have hApow : analyticOrderAt ((fun w : ℂ => 1 - w ^ 2 / τ ^ 2) ^ m) (star τ) = 0 := by
      rw [analyticOrderAt_pow (hAanalytic (star τ)) m, hA]
      simp
    have hBpow : analyticOrderAt ((fun w : ℂ => 1 - w ^ 2 / (star τ) ^ 2) ^ m) (star τ) = m := by
      rw [analyticOrderAt_pow (hBanalytic (star τ)) m, hB]
      simp
    rw [hprod, hApow, hBpow]
    simp
  · subst z
    have hAne : 1 - (-(star τ)) ^ 2 / τ ^ 2 ≠ 0 :=
      oneMinusSquareDiv_ne_zero_of_not_roots hτ hnegstarτ hnegstarnegτ
    have hA := (hAanalytic (-(star τ))).analyticOrderAt_eq_zero.mpr hAne
    have hB := oneMinusSquareDiv_order_one hstar (Or.inr rfl)
    have hApow : analyticOrderAt ((fun w : ℂ => 1 - w ^ 2 / τ ^ 2) ^ m) (-(star τ)) = 0 := by
      rw [analyticOrderAt_pow (hAanalytic (-(star τ))) m, hA]
      simp
    have hBpow : analyticOrderAt ((fun w : ℂ => 1 - w ^ 2 / (star τ) ^ 2) ^ m) (-(star τ)) = m := by
      rw [analyticOrderAt_pow (hBanalytic (-(star τ))) m, hB]
      simp
    rw [hprod, hApow, hBpow]
    simp

/-- A positive real height and a positive displacement make the four signed conjugate roots
distinct; this is a geometric fact, not part of the external zero-count certificate. -/
lemma sigmaDisplacedFirstPoleRoot_distinct (γ d : ℝ) (hγ : 0 < γ) (hd : 0 < d) :
    ((γ : ℂ) + Complex.I * (d : ℂ)) ≠
        star ((γ : ℂ) + Complex.I * (d : ℂ)) ∧
      ((γ : ℂ) + Complex.I * (d : ℂ)) ≠
        -star ((γ : ℂ) + Complex.I * (d : ℂ)) := by
  constructor
  · intro h
    have him := congrArg Complex.im h
    have hreal : d = -d := by simpa using him
    linarith
  · intro h
    have hre := congrArg Complex.re h
    have hreal : γ = -γ := by simpa using hre
    linarith

/-- The explicit normalized factor has exactly the four signed conjugate roots when its
multiplicity is positive and the first root is nonzero. -/
lemma sigmaDisplacedFirstPoleFactor_zero_iff
    (τ : ℂ) (m : ℕ) (hm : 0 < m) (hτ : τ ≠ 0) (z : ℂ) :
    sigmaDisplacedFirstPoleFactor τ m z = 0 ↔ sigmaDisplacedFirstPoleRoot τ z := by
  unfold sigmaDisplacedFirstPoleFactor sigmaDisplacedFirstPoleRoot
  constructor
  · intro hz
    have hpow := mul_eq_zero.mp hz
    rcases hpow with hleft | hright
    · have hbase : 1 - z ^ 2 / τ ^ 2 = 0 :=
        ((pow_eq_zero_iff').mp hleft).1
      rcases (oneMinusSquareDiv_zero_iff hτ).mp hbase with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · have hstar : star τ ≠ 0 := by simpa using hτ
      have hbase : 1 - z ^ 2 / (star τ) ^ 2 = 0 :=
        ((pow_eq_zero_iff').mp hright).1
      rcases (oneMinusSquareDiv_zero_iff hstar).mp hbase with h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
  · rintro (h | h | h | h)
    · subst z
      apply mul_eq_zero.mpr
      left
      apply (pow_eq_zero_iff').2
      exact ⟨by simp [hτ], hm.ne'⟩
    · subst z
      apply mul_eq_zero.mpr
      left
      apply (pow_eq_zero_iff').2
      exact ⟨by simp [hτ], hm.ne'⟩
    · subst z
      have hstar : star τ ≠ 0 := by simpa using hτ
      apply mul_eq_zero.mpr
      right
      apply (pow_eq_zero_iff').2
      exact ⟨sub_eq_zero.mpr (div_self (pow_ne_zero 2 hstar)).symm, hm.ne'⟩
    · subst z
      have hstar : star τ ≠ 0 := by simpa using hτ
      apply mul_eq_zero.mpr
      right
      apply (pow_eq_zero_iff').2
      have hneg : (-(star τ)) ^ 2 = (star τ) ^ 2 := by ring
      have hbase : 1 - (-(star τ)) ^ 2 / (star τ) ^ 2 = 0 := by
        rw [hneg]
        exact sub_eq_zero.mpr (div_self (pow_ne_zero 2 hstar)).symm
      exact ⟨hbase, hm.ne'⟩

/-- Explicit certificate interface for isolating exactly the four shifted points in a disk.
`source_zero_set` and `source_order` are the external geometric obligations for the source. The
remaining fields are elementary range and multiplicity facts; the four-root distinctness and
all zero, order, and isolation properties of the displayed polynomial factor are proved below.
Only `source_zero_set` and `source_order` require external zero information. -/
structure SigmaDisplacedProductIsolation (d γ r : ℝ) (m : ℕ) where
  radius_pos : 0 < r
  multiplicity_pos : 0 < m
  height_pos : 0 < γ
  displacement_pos : 0 < d
  displacement_lt_quarter : d < (1 / 4 : ℝ)
  first_pair_inside : ‖(γ : ℂ) + Complex.I * (d : ℂ)‖ < r
  source_zero_set : ∀ z : ℂ, ‖z‖ < r →
    ((completedNativeDisplacedProductContinuation d z = 0) ↔
      sigmaDisplacedFirstPoleRoot ((γ : ℂ) + Complex.I * (d : ℂ)) z)
  source_order : ∀ z : ℂ, ‖z‖ < r →
    sigmaDisplacedFirstPoleRoot ((γ : ℂ) + Complex.I * (d : ℂ)) z →
      analyticOrderAt (completedNativeDisplacedProductContinuation d) z = m

/-- An exact isolation certificate for the continued source product gives the requested local
factorization with an analytic, nowhere-zero quotient. This is the conditional B theorem: the
certificate contains only the source's zero set and exact orders, never the quotient or the
decomposition itself. -/
theorem completedNativeDisplacedProduct_factorization_of_isolation
    (d γ r : ℝ) (m : ℕ)
    (hisolation : SigmaDisplacedProductIsolation d γ r m) :
    ∃ H : ℂ → ℂ,
      (∀ z ∈ Metric.ball 0 r, AnalyticAt ℂ H z) ∧
      (∀ z ∈ Metric.ball 0 r,
        completedNativeDisplacedProductContinuation d z =
          sigmaDisplacedFirstPoleFactor ((γ : ℂ) + Complex.I * (d : ℂ)) m z * H z) ∧
      (∀ z ∈ Metric.ball 0 r, H z ≠ 0) ∧
      (∀ z ∈ Metric.ball 0 r, H (-z) = H z) ∧ deriv H 0 = 0 := by
  let U : Set ℂ := Metric.ball 0 r
  let D : ℂ → ℂ := completedNativeDisplacedProductContinuation d
  let P : ℂ → ℂ := sigmaDisplacedFirstPoleFactor
    ((γ : ℂ) + Complex.I * (d : ℂ)) m
  have hU : IsOpen U := by
    change IsOpen (Metric.ball (0 : ℂ) r)
    exact Metric.isOpen_ball
  have hD : ∀ z ∈ U, AnalyticAt ℂ D z := by
    intro z _hz
    exact completedNativeDisplacedProductContinuation_analyticAt d z
  have hP : ∀ z ∈ U, AnalyticAt ℂ P z := by
    intro z _hz
    change AnalyticAt ℂ
      (sigmaDisplacedFirstPoleFactor ((γ : ℂ) + Complex.I * (d : ℂ)) m) z
    fun_prop [sigmaDisplacedFirstPoleFactor]
  have hτ : (γ : ℂ) + Complex.I * (d : ℂ) ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    have hreal : γ = 0 := by simpa using hre
    linarith [hisolation.height_pos]
  have hrootsDistinct := sigmaDisplacedFirstPoleRoot_distinct γ d
    hisolation.height_pos hisolation.displacement_pos
  have hzeros : ∀ z ∈ U, D z = 0 ↔ P z = 0 := by
    intro z hz
    have hzr : ‖z‖ < r := by
      simpa [U, Metric.mem_ball, dist_eq_norm] using hz
    have hsource := @SigmaDisplacedProductIsolation.source_zero_set d γ r m hisolation z hzr
    have hfactor := sigmaDisplacedFirstPoleFactor_zero_iff
      ((γ : ℂ) + Complex.I * (d : ℂ)) m hisolation.multiplicity_pos hτ z
    simpa [D, P] using hsource.trans hfactor.symm
  have horders : ∀ z ∈ U, P z = 0 →
      analyticOrderAt D z = m ∧ analyticOrderAt P z = m := by
    intro z hzU hzP
    have hzr : ‖z‖ < r := by
      simpa [U, Metric.mem_ball, dist_eq_norm] using hzU
    have hzRoot : sigmaDisplacedFirstPoleRoot
        ((γ : ℂ) + Complex.I * (d : ℂ)) z :=
      (sigmaDisplacedFirstPoleFactor_zero_iff
        ((γ : ℂ) + Complex.I * (d : ℂ)) m hisolation.multiplicity_pos
        hτ z).mp hzP
    exact ⟨@SigmaDisplacedProductIsolation.source_order d γ r m hisolation z hzr hzRoot,
      sigmaDisplacedFirstPoleFactor_order
        ((γ : ℂ) + Complex.I * (d : ℂ)) m hτ
        hrootsDistinct.1 hrootsDistinct.2 z hzRoot⟩
  have hisolated : ∀ z ∈ U, P z = 0 →
      ∀ᶠ w : ℂ in 𝓝 z, P w = 0 → w = z := by
    intro z hzU hzP
    have hzr : ‖z‖ < r := by
      simpa [U, Metric.mem_ball, dist_eq_norm] using hzU
    have hzRoot : sigmaDisplacedFirstPoleRoot
        ((γ : ℂ) + Complex.I * (d : ℂ)) z :=
      (sigmaDisplacedFirstPoleFactor_zero_iff
        ((γ : ℂ) + Complex.I * (d : ℂ)) m hisolation.multiplicity_pos hτ z).mp hzP
    have horderP := sigmaDisplacedFirstPoleFactor_order
      ((γ : ℂ) + Complex.I * (d : ℂ)) m hτ
      hrootsDistinct.1 hrootsDistinct.2 z hzRoot
    obtain ⟨q, hq, hq0, hfactor⟩ := (hP z hzU).analyticOrderAt_eq_natCast.mp horderP
    have hqne : ∀ᶠ w : ℂ in 𝓝 z, q w ≠ 0 := hq.continuousAt.eventually_ne hq0
    filter_upwards [hfactor, hqne] with w hwfactor hwq
    intro hwP
    have hmul : (w - z) ^ m * q w = 0 := by
      rw [hwfactor] at hwP
      simpa [smul_eq_mul] using hwP
    rcases mul_eq_zero.mp hmul with hpow | hqzero
    · exact sub_eq_zero.mp ((pow_eq_zero_iff').mp hpow).1
    · exact (hwq hqzero).elim
  obtain ⟨H, hHanalytic, hHfactor, hHnonzero⟩ :=
    analyticQuotientExtension_of_isolated_zeros U hU D P m hD hP hzeros
      horders hisolated
  refine ⟨H, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact hHanalytic z (by simpa [U] using hz)
  · intro z hz
    simpa [D, P] using hHfactor z (by simpa [U] using hz)
  · intro z hz
    exact hHnonzero z (by simpa [U] using hz)
  · have hPeven (z : ℂ) : P (-z) = P z := by
      simp [P, sigmaDisplacedFirstPoleFactor]
    have hPzero : P 0 ≠ 0 := by
      simp [P, sigmaDisplacedFirstPoleFactor]
    have hzeroU : (0 : ℂ) ∈ U := by simpa [U] using hisolation.radius_pos
    have hPnonzero : ∀ᶠ z : ℂ in 𝓝 0, P z ≠ 0 :=
      (hP 0 hzeroU).continuousAt.eventually_ne hPzero
    have hUevent : ∀ᶠ z : ℂ in 𝓝 0, z ∈ U := hU.mem_nhds hzeroU
    have hNegUevent : ∀ᶠ z : ℂ in 𝓝 0, -z ∈ U := by
      have hnegTendsto : Tendsto (fun z : ℂ => -z) (𝓝 0) (𝓝 0) := by
        simpa using (continuous_neg.continuousAt (x := (0 : ℂ))).tendsto
      exact hnegTendsto.eventually (hU.mem_nhds hzeroU)
    have hnear : H =ᶠ[𝓝 0] (fun z : ℂ => H (-z)) := by
      filter_upwards [hUevent, hNegUevent, hPnonzero] with z hzU hnegU hPz
      have hmul : P z * H z = P z * H (-z) := by
        calc
          P z * H z = D z := (hHfactor z hzU).symm
          _ = D (-z) := (completedNativeDisplacedProductContinuation_even d z).symm
          _ = P (-z) * H (-z) := hHfactor (-z) hnegU
          _ = P z * H (-z) := by rw [hPeven]
      exact (mul_left_cancel₀ hPz hmul)
    have hHanalyticOn : AnalyticOnNhd ℂ H U := fun z hz => hHanalytic z hz
    have hHnegOn : AnalyticOnNhd ℂ (fun z : ℂ => H (-z)) U := by
      intro z hz
      have hzR : ‖z‖ < r := by
        simpa [U, Metric.mem_ball, dist_eq_norm] using hz
      have hnegR : ‖-z‖ < r := by simpa [norm_neg] using hzR
      have hnegU : -z ∈ U := by simpa [U, Metric.mem_ball, dist_eq_norm] using hnegR
      exact (hHanalytic (-z) hnegU).comp (by fun_prop)
    have hballPre : IsPreconnected U := by
      change IsPreconnected (Metric.ball (0 : ℂ) r)
      exact (convex_ball (0 : ℂ) r).isPreconnected
    have hEvenOn : ∀ z ∈ U, H (-z) = H z :=
      AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hHnegOn hHanalyticOn hballPre
        hzeroU hnear.symm
    constructor
    · intro z hz
      exact hEvenOn z (by simpa [U] using hz)
    · have hEvenEvent : ∀ᶠ z : ℂ in 𝓝 0, H (-z) = H z := by
        filter_upwards [hU.mem_nhds hzeroU] with z hz
        exact hEvenOn z hz
      exact analyticAt_deriv_eq_zero_of_even H (hHanalytic 0 hzeroU) hEvenEvent

/-- On the admissible displacement range, the continuation factorization has the same germ as
the original native displaced product. This is the explicit provenance bridge for the quotient
constructed from the entire extension. -/
theorem displacedProductC_native_germ_factorization_of_isolation
    (d γ r : ℝ) (m : ℕ)
    (hisolation : SigmaDisplacedProductIsolation d γ r m) :
    ∃ H : ℂ → ℂ,
      (∀ z ∈ Metric.ball 0 r, AnalyticAt ℂ H z) ∧
      (∀ z ∈ Metric.ball 0 r, H z ≠ 0) ∧
      (∀ z ∈ Metric.ball 0 r, H (-z) = H z) ∧
      (∀ᶠ z : ℂ in 𝓝 0,
        displacedProductC d z =
          sigmaDisplacedFirstPoleFactor ((γ : ℂ) + Complex.I * (d : ℂ)) m z * H z) := by
  obtain ⟨H, hHanalytic, hfactor, hHnonzero, hHeven⟩ :=
    completedNativeDisplacedProduct_factorization_of_isolation d γ r m hisolation
  have hd₁ : -(1 / 2 : ℝ) < d := by linarith [hisolation.displacement_pos]
  have hd₂ : d < (1 / 2 : ℝ) := by linarith [hisolation.displacement_lt_quarter]
  have hnative := completedNativeDisplacedProductContinuation_eq_native_eventually d hd₁ hd₂
  have hball : ∀ᶠ z : ℂ in 𝓝 0, z ∈ Metric.ball 0 r :=
    Metric.ball_mem_nhds 0 hisolation.radius_pos
  refine ⟨H, hHanalytic, hHnonzero, hHeven.1, ?_⟩
  filter_upwards [hnative, hball] with z hsource hz
  simpa only [hsource] using hfactor z hz

/-- Isolation also gives the local analytic removal of the logarithmic derivative at the center.
The auxiliary quotient `q` is constructed from the analytic order of `H'`; no value for the
remainder is supplied as input. This is the center-removal step for checkpoint C. -/
theorem completedNativeDisplacedProduct_logderivative_removable_at_center
    (d γ r : ℝ) (m : ℕ)
    (hisolation : SigmaDisplacedProductIsolation d γ r m) :
    ∃ H q : ℂ → ℂ,
      AnalyticAt ℂ H 0 ∧ H 0 ≠ 0 ∧ AnalyticAt ℂ q 0 ∧
      (∀ᶠ z : ℂ in 𝓝 0, deriv H z = z * q z) ∧
      AnalyticAt ℂ (fun z : ℂ =>
        if z = 0 then -q z / (4 * H z) else -deriv H z / (4 * z * H z)) 0 := by
  obtain ⟨H, hHanalytic, _hfactor, hHnonzero, _hHeven, hHderiv0⟩ :=
    completedNativeDisplacedProduct_factorization_of_isolation d γ r m hisolation
  have hzeroU : (0 : ℂ) ∈ Metric.ball 0 r := by
    exact Metric.mem_ball_self hisolation.radius_pos
  have hH0 : H 0 ≠ 0 := hHnonzero 0 hzeroU
  have hHanalytic0 : AnalyticAt ℂ H 0 := hHanalytic 0 hzeroU
  have hderivAnalytic : AnalyticAt ℂ (deriv H) 0 := hHanalytic0.deriv
  obtain ⟨q, hq, hqfactor⟩ := analyticAt_factor_by_id_of_zero (deriv H)
    hderivAnalytic hHderiv0
  have hremoved := analyticLogDerivative_div_t_analyticAt_zero H q hHanalytic0 hH0
    hq hqfactor
  exact ⟨H, q, hHanalytic0, hH0, hq, hqfactor, hremoved⟩

/-- Under the source zero-isolation certificate, the regularized logarithmic derivative of the
constructed remainder is analytic throughout the `t` disk. This completes the singularity
removal in C, before descent to the quadratic variable. -/
theorem completedNativeDisplacedProduct_logremainderT_analytic_of_isolation
    (d γ r : ℝ) (m : ℕ)
    (hisolation : SigmaDisplacedProductIsolation d γ r m) :
    ∃ H q : ℂ → ℂ,
      (∀ z ∈ Metric.ball 0 r, AnalyticAt ℂ H z) ∧
      (∀ z ∈ Metric.ball 0 r, H z ≠ 0) ∧
      (∀ z ∈ Metric.ball 0 r, H (-z) = H z) ∧
      (∀ᶠ z : ℂ in 𝓝 0, deriv H z = z * q z) ∧
      AnalyticOnNhd ℂ (sigmaDisplacedLogRemainderT H q) (Metric.ball 0 r) := by
  obtain ⟨H, hHanalytic, _hfactor, hHnonzero, hHeven, hHderiv0⟩ :=
    completedNativeDisplacedProduct_factorization_of_isolation d γ r m hisolation
  have hzeroU : (0 : ℂ) ∈ Metric.ball 0 r :=
    Metric.mem_ball_self hisolation.radius_pos
  have hderivAnalytic : AnalyticAt ℂ (deriv H) 0 :=
    (hHanalytic 0 hzeroU).deriv
  obtain ⟨q, hq, hqfactor⟩ := analyticAt_factor_by_id_of_zero (deriv H)
    hderivAnalytic hHderiv0
  have hrem := sigmaDisplacedLogRemainderT_analyticOnNhd r hisolation.radius_pos H q
    hHanalytic hHnonzero hq hqfactor
  exact ⟨H, q, hHanalytic, hHnonzero, hHeven, hqfactor, hrem⟩

/-- The isolation certificate yields an analytic even remainder function in `t` on the full
source disk. The remaining C step is descent to `u = t²` and coefficient identification. -/
theorem completedNativeDisplacedProduct_logremainderT_analytic_even_of_isolation
    (d γ r : ℝ) (m : ℕ)
    (hisolation : SigmaDisplacedProductIsolation d γ r m) :
    ∃ H q : ℂ → ℂ,
      (∀ z ∈ Metric.ball 0 r, AnalyticAt ℂ H z) ∧
      (∀ z ∈ Metric.ball 0 r, H z ≠ 0) ∧
      (∀ z ∈ Metric.ball 0 r, H (-z) = H z) ∧
      (∀ᶠ z : ℂ in 𝓝 0, deriv H z = z * q z) ∧
      AnalyticOnNhd ℂ (sigmaDisplacedLogRemainderT H q) (Metric.ball 0 r) ∧
      (∀ z ∈ Metric.ball 0 r,
        sigmaDisplacedLogRemainderT H q (-z) = sigmaDisplacedLogRemainderT H q z) := by
  obtain ⟨H, q, hHanalytic, hHnonzero, hHeven, hqfactor, hrem⟩ :=
    completedNativeDisplacedProduct_logremainderT_analytic_of_isolation d γ r m hisolation
  refine ⟨H, q, hHanalytic, hHnonzero, hHeven, hqfactor, hrem, ?_⟩
  intro z hz
  exact sigmaDisplacedLogRemainderT_even r H q hHanalytic hHnonzero hHeven z hz

end
end CarrySigmaObstruction

#print axioms CarrySigmaObstruction.analyticQuotientExtension_of_isolated_zeros
#print axioms CarrySigmaObstruction.analyticAt_deriv_eq_zero_of_even
#print axioms CarrySigmaObstruction.analyticAt_factor_by_id_of_zero
#print axioms CarrySigmaObstruction.analyticLogDerivative_div_t_analyticAt_zero
#print axioms CarrySigmaObstruction.sigmaDisplacedLogRemainderT_analyticOnNhd
#print axioms CarrySigmaObstruction.analyticOnNhd_even_deriv_neg
#print axioms CarrySigmaObstruction.sigmaDisplacedLogRemainderT_even
#print axioms CarrySigmaObstruction.oneMinusSquareDiv_zero_iff
#print axioms CarrySigmaObstruction.sigmaDisplacedFirstPoleFactor_zero_iff
#print axioms CarrySigmaObstruction.sigmaDisplacedFirstPoleFactor_order
#print axioms CarrySigmaObstruction.sigmaDisplacedFirstPoleRoot_distinct
#print axioms CarrySigmaObstruction.completedNativeDisplacedProduct_factorization_of_isolation
#print axioms CarrySigmaObstruction.displacedProductC_native_germ_factorization_of_isolation
#print axioms CarrySigmaObstruction.completedNativeDisplacedProduct_logderivative_removable_at_center
#print axioms CarrySigmaObstruction.completedNativeDisplacedProduct_logremainderT_analytic_of_isolation
#print axioms CarrySigmaObstruction.completedNativeDisplacedProduct_logremainderT_analytic_even_of_isolation
