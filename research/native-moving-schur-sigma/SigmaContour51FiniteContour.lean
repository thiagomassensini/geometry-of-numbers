import SigmaContour51Residue

/-!
# The circle integral of an interior simple-pole kernel

The logarithmic-derivative residue calculation reduces the global contour identity to Cauchy's
formula plus the integral of `(z - a)⁻¹ z^(-k)`. This module proves that this integral is zero
for every positive integer `k`, using Mathlib's circle-integral formulas for inverse powers.
-/

namespace CarrySigmaObstruction

open Complex Set Metric Filter Topology
open CarrySelfAdjointOperator CarrySigmaSource

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

def contour51PoleKernel (a : ℂ) (n : ℕ) : ℂ → ℂ :=
  fun z => (z - a)⁻¹ * z ^ (-((n + 1 : ℕ) : ℤ))

/-- Every positive-order Cauchy kernel with an interior simple pole has zero integral after the
origin pole of order `n+1` is included. This is the partial-fraction cancellation needed by C2. -/
theorem contour51_pole_kernel_integrable_and_integral_zero
    (a : ℂ) (n : ℕ) (ha : a ∈ ball (0 : ℂ) 51) (ha0 : a ≠ 0) :
    CircleIntegrable (contour51PoleKernel a n) 0 51 ∧
      (∮ z in C(0, 51), contour51PoleKernel a n z) = 0 := by
  have haNorm : ‖a‖ < 51 := by simpa [Metric.mem_ball, dist_eq_norm] using ha
  have hzInv : CircleIntegrable (fun z : ℂ => (z - a)⁻¹) 0 51 := by
    rw [circleIntegrable_sub_inv_iff]
    right
    intro hz
    have hzNorm : ‖a‖ = 51 := by simpa using mem_sphere_iff_norm.mp hz
    exact (ne_of_lt haNorm) hzNorm
  have hzeroInv : CircleIntegrable (fun z : ℂ => z⁻¹) 0 51 := by
    simpa [sub_zero] using
      (circleIntegrable_sub_inv_iff (c := (0 : ℂ)) (w := (0 : ℂ))
        (R := (51 : ℝ))).2 (Or.inr (by simp))
  induction n with
  | zero =>
      have hEq : EqOn (contour51PoleKernel a 0)
          (fun z => a⁻¹ • ((z - a)⁻¹ - z⁻¹)) (sphere (0 : ℂ) 51) := by
        intro z hz
        have hzNorm : ‖z‖ = 51 := by simpa using mem_sphere_iff_norm.mp hz
        have hz0 : z ≠ 0 := by
          intro h
          subst z
          norm_num at hzNorm
        have hza : z ≠ a := by
          intro h
          rw [h] at hzNorm
          exact (ne_of_lt haNorm) hzNorm
        change (z - a)⁻¹ * z ^ (-((0 + 1 : ℕ) : ℤ)) =
          a⁻¹ * ((z - a)⁻¹ - z⁻¹)
        norm_num [zpow_neg, zpow_one]
        field_simp [ha0, hza, hz0]
        ring
      have hsum : CircleIntegrable
          (fun z : ℂ => a⁻¹ • ((z - a)⁻¹ - z⁻¹)) 0 51 :=
        (hzInv.sub hzeroInv).const_smul
      have hkernel : CircleIntegrable (contour51PoleKernel a 0) 0 51 :=
        (circleIntegrable_congr (by simpa using hEq)).2 hsum
      refine ⟨hkernel, ?_⟩
      calc
        (∮ z in C(0, 51), contour51PoleKernel a 0 z) =
            ∮ z in C(0, 51), a⁻¹ • ((z - a)⁻¹ - z⁻¹) :=
          circleIntegral.integral_congr (by norm_num) hEq
        _ = a⁻¹ • ((∮ z in C(0, 51), (z - a)⁻¹) -
              ∮ z in C(0, 51), z⁻¹) := by
          rw [circleIntegral.integral_smul, circleIntegral.integral_sub hzInv hzeroInv]
        _ = 0 := by
          have haInt := circleIntegral.integral_sub_inv_of_mem_ball ha
          have h0Int : (∮ z in C(0, 51), z⁻¹) = 2 * Real.pi * Complex.I := by
            simpa using circleIntegral.integral_sub_center_inv (0 : ℂ) (by norm_num)
          rw [haInt, h0Int]
          simp
  | succ n ih =>
      obtain ⟨hkernelN, hzeroN⟩ := ih
      let p : ℂ → ℂ := fun z => z ^ (-((n + 2 : ℕ) : ℤ))
      have hp : CircleIntegrable p 0 51 := by
        have hnot : (0 : ℂ) ∉ sphere (0 : ℂ) |(51 : ℝ)| := by simp
        have h := (circleIntegrable_sub_zpow_iff
          (c := (0 : ℂ)) (w := (0 : ℂ)) (R := (51 : ℝ))
          (n := -((n + 2 : ℕ) : ℤ))).2 (Or.inr (Or.inr hnot))
        simpa [p] using h
      have hEq : EqOn (contour51PoleKernel a (n + 1))
          (fun z => a⁻¹ • (contour51PoleKernel a n z - p z))
          (sphere (0 : ℂ) 51) := by
        intro z hz
        have hzNorm : ‖z‖ = 51 := by simpa using mem_sphere_iff_norm.mp hz
        have hz0 : z ≠ 0 := by
          intro h
          subst z
          norm_num at hzNorm
        have hza : z ≠ a := by
          intro h
          rw [h] at hzNorm
          exact (ne_of_lt haNorm) hzNorm
        change (z - a)⁻¹ * z ^ (-((n + 1 + 1 : ℕ) : ℤ)) =
          a⁻¹ * ((z - a)⁻¹ * z ^ (-((n + 1 : ℕ) : ℤ)) -
            z ^ (-((n + 2 : ℕ) : ℤ)))
        norm_num [zpow_neg]
        field_simp [ha0, hza, hz0]
        have hpow : z ^ (-2 - (n : ℤ)) * z = z ^ (-1 - (n : ℤ)) := by
          calc
            z ^ (-2 - (n : ℤ)) * z =
                z ^ (-2 - (n : ℤ)) * z ^ (1 : ℤ) := by simp
            _ = z ^ ((-2 - (n : ℤ)) + 1) := by rw [← zpow_add₀ hz0]
            _ = z ^ (-1 - (n : ℤ)) := by congr 1; omega
        rw [show z ^ (-1 + (-1 + -(n : ℤ))) = z ^ (-2 - (n : ℤ)) by
              congr 1; omega,
            show z ^ (-1 + -(n : ℤ)) = z ^ (-1 - (n : ℤ)) by rfl,
            show z ^ (-2 + -(n : ℤ)) = z ^ (-2 - (n : ℤ)) by rfl]
        have hdist : (z - a) * z ^ (-2 - (n : ℤ)) =
            z * z ^ (-2 - (n : ℤ)) - a * z ^ (-2 - (n : ℤ)) := by ring
        rw [hdist, mul_comm z (z ^ (-2 - (n : ℤ))), hpow]
        ring
      have hsum : CircleIntegrable
          (fun z : ℂ => a⁻¹ • (contour51PoleKernel a n z - p z)) 0 51 :=
        (hkernelN.sub hp).const_smul
      have hkernel : CircleIntegrable (contour51PoleKernel a (n + 1)) 0 51 :=
        (circleIntegrable_congr (by simpa using hEq)).2 hsum
      refine ⟨hkernel, ?_⟩
      calc
        (∮ z in C(0, 51), contour51PoleKernel a (n + 1) z) =
            ∮ z in C(0, 51), a⁻¹ • (contour51PoleKernel a n z - p z) :=
          circleIntegral.integral_congr (by norm_num) hEq
        _ = a⁻¹ • ((∮ z in C(0, 51), contour51PoleKernel a n z) -
              ∮ z in C(0, 51), p z) := by
          rw [circleIntegral.integral_smul,
            circleIntegral.integral_sub hkernelN hp]
        _ = 0 := by
          rw [hzeroN]
          have hpow : (∮ z in C(0, 51), p z) = 0 := by
            have hexp : -((n + 2 : ℕ) : ℤ) ≠ -1 := by omega
            simpa [p, sub_zero] using
              (circleIntegral.integral_sub_zpow_of_ne hexp
                (0 : ℂ) (0 : ℂ) (51 : ℝ))
          rw [hpow]
          simp

/-- If an analytic correction removes a finite set of interior simple-pole kernels from a
boundary response, its normalized circle integral is the corresponding Cauchy coefficient.
This packages the global integral step conditionally on the corrected function being regular. -/
theorem contour51_cauchy_reduction_of_finite_correction
    (R G : ℂ → ℂ) (poles : Finset ℂ) (n : ℕ)
    (hG : DiffContOnCl ℂ G (ball (0 : ℂ) 51))
    (hRInt : CircleIntegrable (fun z => R z / z ^ (n + 1)) 0 51)
    (hpoles : ∀ a ∈ poles, a ∈ ball (0 : ℂ) 51 ∧ a ≠ 0)
    (hcorr : EqOn (fun z => G z / z ^ (n + 1))
      (fun z => R z / z ^ (n + 1) +
        ∑ a ∈ poles, (1 / 2 : ℂ) * contour51PoleKernel a n z)
      (sphere (0 : ℂ) 51)) :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ •
      ∮ z in C(0, 51), R z / z ^ (n + 1) =
        iteratedDeriv n G 0 / (n.factorial : ℂ) := by
  have htermInt : ∀ a ∈ poles,
      CircleIntegrable (fun z => (1 / 2 : ℂ) * contour51PoleKernel a n z) 0 51 := by
    intro a ha
    obtain ⟨haBall, ha0⟩ := hpoles a ha
    exact (contour51_pole_kernel_integrable_and_integral_zero a n haBall ha0).1.const_smul
  have hsumInt : CircleIntegrable
      (fun z => ∑ a ∈ poles, (1 / 2 : ℂ) * contour51PoleKernel a n z) 0 51 :=
    CircleIntegrable.fun_sum poles htermInt
  have htermZero : ∀ a ∈ poles,
      (∮ z in C(0, 51), (1 / 2 : ℂ) * contour51PoleKernel a n z) = 0 := by
    intro a ha
    obtain ⟨haBall, ha0⟩ := hpoles a ha
    have hzero :=
      (contour51_pole_kernel_integrable_and_integral_zero a n haBall ha0).2
    calc
      (∮ z in C(0, 51), (1 / 2 : ℂ) * contour51PoleKernel a n z) =
          (1 / 2 : ℂ) * (∮ z in C(0, 51), contour51PoleKernel a n z) :=
        circleIntegral.integral_const_mul (1 / 2 : ℂ) (contour51PoleKernel a n) 0 51
      _ = 0 := by rw [hzero]; simp
  have hsumZero : (∮ z in C(0, 51),
      ∑ a ∈ poles, (1 / 2 : ℂ) * contour51PoleKernel a n z) = 0 := by
    rw [circleIntegral.integral_fun_sum htermInt]
    exact Finset.sum_eq_zero htermZero
  have hGintegral :
      (∮ z in C(0, 51), G z / z ^ (n + 1)) =
        (∮ z in C(0, 51), R z / z ^ (n + 1)) +
          (∮ z in C(0, 51),
            ∑ a ∈ poles, (1 / 2 : ℂ) * contour51PoleKernel a n z) := by
    calc
      (∮ z in C(0, 51), G z / z ^ (n + 1)) =
          ∮ z in C(0, 51),
            (fun z => R z / z ^ (n + 1) +
              ∑ a ∈ poles, (1 / 2 : ℂ) * contour51PoleKernel a n z) z :=
        circleIntegral.integral_congr (by norm_num) hcorr
      _ = _ := circleIntegral.integral_add hRInt hsumInt
  have hsame :
      (∮ z in C(0, 51), G z / z ^ (n + 1)) =
        (∮ z in C(0, 51), R z / z ^ (n + 1)) := by
    rw [hGintegral, hsumZero]
    ring
  have hCauchy := normalized_circle_integral_coefficient G n hG
  calc
    (2 * Real.pi * Complex.I : ℂ)⁻¹ •
        ∮ z in C(0, 51), R z / z ^ (n + 1) =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ •
        ∮ z in C(0, 51), G z / z ^ (n + 1) := by rw [hsame]
    _ = iteratedDeriv n G 0 / (n.factorial : ℂ) := hCauchy

/-- A finite list of simple zeros lets the local pole cancellations glue into a corrected
analytic function on the closed radius-51 disk. The theorem then invokes the conditional Cauchy
reduction above. -/
theorem exists_contour51_corrected_log_derivative
    (F : ℂ → ℂ) (poles : Finset ℂ) (n : ℕ)
    (hF : ∀ z, AnalyticAt ℂ F z)
    (hzeros : ∀ z, z ∈ closedBall (0 : ℂ) 51 → (F z = 0 ↔ z ∈ poles))
    (horder : ∀ a ∈ poles, analyticOrderAt F a = 1)
    (hinside : ∀ a ∈ poles, ‖a‖ < 51)
    (hF0 : F 0 ≠ 0) :
    ∃ G, DiffContOnCl ℂ G (ball (0 : ℂ) 51) ∧
      (2 * Real.pi * Complex.I : ℂ)⁻¹ •
        ∮ z in C(0, 51), (-deriv F z / ((2 : ℂ) * F z)) / z ^ (n + 1) =
          iteratedDeriv n G 0 / (n.factorial : ℂ) ∧
      iteratedDeriv n G 0 / (n.factorial : ℂ) =
        iteratedDeriv n (fun z => -deriv F z / ((2 : ℂ) * F z)) 0 /
            (n.factorial : ℂ) -
          (1 / 2 : ℂ) * ∑ a ∈ poles, a ^ (-1 - (n : ℤ)) := by
  classical
  let response : ℂ → ℂ := fun z => -deriv F z / ((2 : ℂ) * F z)
  let poleTerm : ℂ → ℂ → ℂ := fun a z => (1 / 2 : ℂ) / (z - a)
  have hlocal : ∀ a, a ∈ poles →
      ∃ H : ℂ → ℂ, AnalyticAt ℂ H a ∧
        H =ᶠ[𝓝[≠] a] fun z => response z + poleTerm a z := by
    intro a ha
    simpa [response, poleTerm, div_eq_mul_inv, mul_comm] using
      (analytic_simple_zero_log_derivative_pole_cancellation (hF a) (horder a ha))
  choose H hHanalytic hHnear using hlocal
  have hPoleAnalytic : ∀ a b : ℂ, a ≠ b →
      AnalyticAt ℂ (fun w => poleTerm a w) b := by
    intro a b hab
    dsimp [poleTerm]
    exact (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (1 / 2 : ℂ)) b).div
      (analyticAt_id.sub (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => a) b))
      (sub_ne_zero.mpr hab.symm)
  let G : ℂ → ℂ := fun z =>
    if hz : z ∈ poles then
      H z hz z + ∑ b ∈ poles.erase z, poleTerm b z
    else
      response z + ∑ b ∈ poles, poleTerm b z
  have hGanalytic : ∀ z, z ∈ closedBall (0 : ℂ) 51 → AnalyticAt ℂ G z := by
    intro z hzball
    by_cases hzPole : z ∈ poles
    · let J : ℂ → ℂ := fun w => H z hzPole w +
        ∑ b ∈ poles.erase z, poleTerm b w
      have hsumEq : (fun w => ∑ b ∈ poles.erase z, poleTerm b w) =
          ∑ b ∈ poles.erase z, fun w => poleTerm b w := by
        funext w
        simp
      have hsumAna : AnalyticAt ℂ (fun w => ∑ b ∈ poles.erase z, poleTerm b w) z := by
        rw [hsumEq]
        exact Finset.analyticAt_sum (poles.erase z) (by
          intro b hb
          have hb' := Finset.mem_erase.mp hb
          exact hPoleAnalytic b z hb'.1)
      have hJanalytic : AnalyticAt ℂ J z := (hHanalytic z hzPole).add hsumAna
      have hnotErase : ∀ᶠ w : ℂ in 𝓝 z, w ∉ poles.erase z := by
        have hclosed : IsClosed ((poles.erase z : Finset ℂ) : Set ℂ) :=
          (poles.erase z).finite_toSet.isClosed
        apply hclosed.isOpen_compl.mem_nhds
        simp
      have hEqPunctured : G =ᶠ[𝓝[≠] z] J := by
        filter_upwards [eventually_nhdsWithin_of_eventually_nhds hnotErase,
          hHnear z hzPole, self_mem_nhdsWithin] with w hwErase hwLocal hwNe
        have hwNotPole : w ∉ poles := by
          intro hwMem
          exact hwErase (Finset.mem_erase.mpr ⟨hwNe, hwMem⟩)
        have hsum : (∑ b ∈ poles, poleTerm b w) =
            poleTerm z w + ∑ b ∈ poles.erase z, poleTerm b w := by
          rw [← Finset.add_sum_erase _ _ hzPole]
        dsimp [G, J]
        rw [dif_neg hwNotPole, hwLocal, hsum]
        ring
      have hEqAt : G z = J z := by
        simp [G, J, hzPole]
      have hEq : G =ᶠ[𝓝 z] J :=
        eventuallyEq_nhds_of_eventuallyEq_nhdsNE hEqPunctured hEqAt
      exact hJanalytic.congr hEq.symm
    · have hFz : F z ≠ 0 := by
        intro hzero
        exact hzPole ((hzeros z hzball).mp hzero)
      have hResponse : AnalyticAt ℂ response z := by
        dsimp [response]
        exact ((hF z).deriv.neg).div (analyticAt_const.mul (hF z))
          (mul_ne_zero (by norm_num) hFz)
      have hsumEq : (fun w => ∑ b ∈ poles, poleTerm b w) =
          ∑ b ∈ poles, fun w => poleTerm b w := by
        funext w
        simp
      have hsumAna : AnalyticAt ℂ (fun w => ∑ b ∈ poles, poleTerm b w) z := by
        rw [hsumEq]
        exact Finset.analyticAt_sum poles (by
          intro b hb
          have hzb : z ≠ b := by
            intro h
            exact hzPole (h ▸ hb)
          exact hPoleAnalytic b z hzb.symm)
      let J : ℂ → ℂ := fun w => response w + ∑ b ∈ poles, poleTerm b w
      have hJanalytic : AnalyticAt ℂ J z := hResponse.add hsumAna
      have hnotPole : ∀ᶠ w : ℂ in 𝓝 z, w ∉ poles := by
        have hclosed : IsClosed (poles : Set ℂ) := poles.finite_toSet.isClosed
        apply hclosed.isOpen_compl.mem_nhds
        exact hzPole
      have hEq : G =ᶠ[𝓝 z] J := by
        filter_upwards [hnotPole] with w hw
        simp [G, J, hw]
      exact hJanalytic.congr hEq.symm
  have hDiffClosed : DifferentiableOn ℂ G (closedBall (0 : ℂ) 51) := by
    intro z hz
    exact (hGanalytic z hz).differentiableAt.differentiableWithinAt
  have hG : DiffContOnCl ℂ G (ball (0 : ℂ) 51) := by
    have hcontinuousClosure : ContinuousOn G (closure (ball (0 : ℂ) 51)) := by
      intro z hz
      exact (hGanalytic z (Metric.closure_ball_subset_closedBall hz)).continuousAt.continuousWithinAt
    exact ⟨hDiffClosed.mono Metric.ball_subset_closedBall, hcontinuousClosure⟩
  have hFnonzeroSphere : ∀ z ∈ sphere (0 : ℂ) 51, F z ≠ 0 := by
    intro z hz
    have hbound : z ∈ closedBall (0 : ℂ) 51 := sphere_subset_closedBall hz
    have hzNorm : ‖z‖ = 51 := by simpa using mem_sphere_iff_norm.mp hz
    intro hzero
    have hzPole := (hzeros z hbound).mp hzero
    exact (ne_of_lt (hinside z hzPole)) hzNorm
  have hResponseContinuous : ContinuousOn response (sphere (0 : ℂ) 51) := by
    dsimp [response]
    apply ContinuousOn.div
    · intro z hz
      exact ((hF z).deriv.neg).continuousAt.continuousWithinAt
    · exact continuousOn_const.mul
        (fun z hz => (hF z).continuousAt.continuousWithinAt)
    · intro z hz
      exact mul_ne_zero (by norm_num) (hFnonzeroSphere z hz)
  have hpowContinuous : ContinuousOn (fun z : ℂ => z ^ (n + 1))
      (sphere (0 : ℂ) 51) := by fun_prop
  have hpowNe : ∀ z ∈ sphere (0 : ℂ) 51, z ^ (n + 1) ≠ 0 := by
    intro z hz
    apply pow_ne_zero
    intro hzero
    have hzNorm : ‖z‖ = 51 := by simpa using mem_sphere_iff_norm.mp hz
    rw [hzero] at hzNorm
    norm_num at hzNorm
  have hRInt : CircleIntegrable (fun z => response z / z ^ (n + 1)) 0 51 :=
    (hResponseContinuous.div hpowContinuous hpowNe).circleIntegrable (by norm_num)
  have hboundary : EqOn (fun z => G z / z ^ (n + 1))
      (fun z => response z / z ^ (n + 1) +
        ∑ a ∈ poles, (1 / 2 : ℂ) * contour51PoleKernel a n z)
      (sphere (0 : ℂ) 51) := by
    intro z hz
    have hzNotPole : z ∉ poles := by
      intro hzPole
      have hzNorm : ‖z‖ = 51 := by simpa using mem_sphere_iff_norm.mp hz
      exact (ne_of_lt (hinside z hzPole)) hzNorm
    have hz0 : z ≠ 0 := by
      intro hzEq
      subst z
      have hzNorm : ‖(0 : ℂ)‖ = 51 := by simpa using mem_sphere_iff_norm.mp hz
      norm_num at hzNorm
    have hGval : G z = response z + ∑ a ∈ poles, poleTerm a z := by
      simp [G, hzNotPole]
    change G z / z ^ (n + 1) =
      response z / z ^ (n + 1) +
        ∑ a ∈ poles, (1 / 2 : ℂ) * contour51PoleKernel a n z
    rw [hGval, add_div, Finset.sum_div]
    congr 1
    apply Finset.sum_congr rfl
    intro a ha
    have hza : z - a ≠ 0 := by
      apply sub_ne_zero.mpr
      intro h
      exact hzNotPole (h ▸ ha)
    dsimp [poleTerm, contour51PoleKernel]
    norm_num [zpow_neg]
    field_simp [hz0, hza]
    have hpow : z ^ (n + 1) * z ^ (-1 - (n : ℤ)) = 1 := by
      rw [pow_succ]
      calc
        z ^ n * z * z ^ (-1 - (n : ℤ)) =
            z ^ (n : ℤ) * z * z ^ (-1 - (n : ℤ)) := by
          rw [show z ^ n = z ^ (n : ℤ) by simp]
        _ = z ^ (n : ℤ) * z ^ (1 : ℤ) * z ^ (-1 - (n : ℤ)) := by simp
        _ = z ^ ((n : ℤ) + 1 + (-1 - (n : ℤ))) := by
          rw [← zpow_add₀ hz0, ← zpow_add₀ hz0]
        _ = 1 := by
          rw [show (n : ℤ) + 1 + (-1 - (n : ℤ)) = 0 by ring, zpow_zero]
    exact hpow.symm
  have hpoles : ∀ a ∈ poles, a ∈ ball (0 : ℂ) 51 ∧ a ≠ 0 := by
    intro a ha
    refine ⟨?_, ?_⟩
    · simpa [Metric.mem_ball, dist_eq_norm] using hinside a ha
    · intro ha0
      subst a
      have hz0 : (0 : ℂ) ∈ closedBall 0 51 := by simp
      exact hF0 ((hzeros 0 hz0).mpr ha)
  refine ⟨G, hG, ?_⟩
  refine ⟨contour51_cauchy_reduction_of_finite_correction
    response G poles n hG hRInt hpoles hboundary, ?_⟩
  have hzeroNotPole : (0 : ℂ) ∉ poles := by
    intro hzeroPole
    exact hF0 ((hzeros 0 (by simp)).2 hzeroPole)
  have hresponse : AnalyticAt ℂ response 0 := by
    dsimp [response]
    exact ((hF 0).deriv.neg).div (analyticAt_const.mul (hF 0))
      (mul_ne_zero (by norm_num) hF0)
  let J : ℂ → ℂ := fun z => response z + ∑ a ∈ poles, poleTerm a z
  have hsumEq : (fun z => ∑ a ∈ poles, poleTerm a z) =
      ∑ a ∈ poles, fun z => poleTerm a z := by
    funext z
    simp
  have hsumAnalytic : AnalyticAt ℂ (fun z => ∑ a ∈ poles, poleTerm a z) 0 := by
    rw [hsumEq]
    exact Finset.analyticAt_sum poles (by
      intro a ha
      have ha0 : a ≠ 0 := by
        intro h
        subst a
        exact hzeroNotPole ha
      exact hPoleAnalytic a 0 ha0)
  have hJanalytic : AnalyticAt ℂ J 0 := hresponse.add hsumAnalytic
  have hnotPole : ∀ᶠ z : ℂ in 𝓝 0, z ∉ poles := by
    have hclosed : IsClosed (poles : Set ℂ) := poles.finite_toSet.isClosed
    exact hclosed.isOpen_compl.mem_nhds hzeroNotPole
  have hGnear : G =ᶠ[𝓝 0] J := by
    filter_upwards [hnotPole] with z hz
    simp [G, J, hz]
  have hGiter : iteratedDeriv n G 0 = iteratedDeriv n J 0 :=
    hGnear.iteratedDeriv_eq n
  have hsumIter : iteratedDeriv n (fun z => ∑ a ∈ poles, poleTerm a z) 0 =
      ∑ a ∈ poles, iteratedDeriv n (fun z => poleTerm a z) 0 := by
    exact iteratedDeriv_fun_sum (by
      intro a ha
      have ha0 : a ≠ 0 := by
        intro h
        subst a
        exact hzeroNotPole ha
      exact (hPoleAnalytic a 0 ha0).contDiffAt)
  have hJiter : iteratedDeriv n J 0 =
      iteratedDeriv n response 0 +
        ∑ a ∈ poles, iteratedDeriv n (fun z => poleTerm a z) 0 := by
    change iteratedDeriv n (response + (fun z => ∑ a ∈ poles, poleTerm a z)) 0 = _
    rw [iteratedDeriv_add hresponse.contDiffAt hsumAnalytic.contDiffAt, hsumIter]
  have htermIter (a : ℂ) (ha : a ∈ poles) :
      iteratedDeriv n (fun z => poleTerm a z) 0 =
        -(1 / 2 : ℂ) * (n.factorial : ℂ) * a ^ (-1 - (n : ℤ)) := by
    have ha0 : a ≠ 0 := by
      intro h
      subst a
      exact hzeroNotPole ha
    have hsign : (-1 : ℂ) ^ n * (-1 : ℂ) ^ (-1 - (n : ℤ)) = -1 := by
      calc
        (-1 : ℂ) ^ n * (-1 : ℂ) ^ (-1 - (n : ℤ)) =
            (-1 : ℂ) ^ ((n : ℤ) + (-1 - (n : ℤ))) := by
          rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
        _ = -1 := by
          rw [show (n : ℤ) + (-1 - (n : ℤ)) = -1 by omega]
          norm_num
    have hnegpow : (-a) ^ (-1 - (n : ℤ)) =
        (-1 : ℂ) ^ (-1 - (n : ℤ)) * a ^ (-1 - (n : ℤ)) := by
      rw [show -a = (-1 : ℂ) * a by ring, mul_zpow]
    change iteratedDeriv n (fun z : ℂ => (1 / 2 : ℂ) * (z - a)⁻¹) 0 = _
    rw [iteratedDeriv_const_mul_field]
    have hlinear := congrFun (iter_deriv_inv_linear n (1 : ℂ) (-a)) 0
    have hinv : iteratedDeriv n (fun z : ℂ => (z - a)⁻¹) 0 =
        (-1 : ℂ) ^ n * (n.factorial : ℂ) * (-a) ^ (-1 - (n : ℤ)) := by
      rw [iteratedDeriv_eq_iterate]
      simpa [sub_eq_add_neg] using hlinear
    rw [hinv, hnegpow]
    calc
      (1 / 2 : ℂ) * ((-1 : ℂ) ^ n * (n.factorial : ℂ) *
          ((-1 : ℂ) ^ (-1 - (n : ℤ)) * a ^ (-1 - (n : ℤ)))) =
        (1 / 2 : ℂ) * (n.factorial : ℂ) *
          (((-1 : ℂ) ^ n * (-1 : ℂ) ^ (-1 - (n : ℤ))) *
            a ^ (-1 - (n : ℤ))) := by ring
      _ = -(1 / 2 : ℂ) * (n.factorial : ℂ) * a ^ (-1 - (n : ℤ)) := by
        rw [hsign]
        ring
  have hsumPole :
      (∑ a ∈ poles, iteratedDeriv n (fun z => poleTerm a z) 0) =
        -(1 / 2 : ℂ) * (n.factorial : ℂ) *
          ∑ a ∈ poles, a ^ (-1 - (n : ℤ)) := by
    calc
      _ = ∑ a ∈ poles,
          (-(1 / 2 : ℂ) * (n.factorial : ℂ) * a ^ (-1 - (n : ℤ))) :=
        Finset.sum_congr rfl (by intro a ha; exact htermIter a ha)
      _ = _ := by rw [Finset.mul_sum]
  have hfact : (n.factorial : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos n).ne'
  rw [hGiter, hJiter, hsumPole]
  simp only [response]
  field_simp [hfact]
  ring

/-- The signed list of the ten positive C1 heights. -/
def contour51SignedTenRoots (ts : Fin 10 → ℝ) : Finset ℂ :=
  Finset.univ.image (fun i : Fin 10 => (ts i : ℂ)) ∪
    Finset.univ.image (fun i : Fin 10 => -(ts i : ℂ))

/-- Pairing the positive and negative C1 roots turns the signed principal-part sum into the ten
positive real modes. -/
theorem contour51_signed_ten_root_power_sum
    (ts : Fin 10 → ℝ) (hmono : StrictMono ts)
    (hpos : ∀ i : Fin 10, 0 < ts i) (n : ℕ) :
    (1 / 2 : ℂ) *
        ∑ a ∈ contour51SignedTenRoots ts,
          a ^ (-1 - ((2 * n + 1 : ℕ) : ℤ)) =
      ∑ i : Fin 10, (ts i : ℂ) ^ (-((2 * n + 2 : ℕ) : ℤ)) := by
  classical
  let q : ℤ := -1 - ((2 * n + 1 : ℕ) : ℤ)
  let pos : Finset ℂ := Finset.univ.image (fun i : Fin 10 => (ts i : ℂ))
  let neg : Finset ℂ := Finset.univ.image (fun i : Fin 10 => -(ts i : ℂ))
  have hq : q = -((2 * n + 2 : ℕ) : ℤ) := by
    dsimp [q]
    omega
  have hposInj : Function.Injective (fun i : Fin 10 => (ts i : ℂ)) := by
    intro i j hij
    apply hmono.injective
    have him := congrArg Complex.re hij
    simpa using him
  have hnegInj : Function.Injective (fun i : Fin 10 => -(ts i : ℂ)) := by
    intro i j hij
    apply hposInj
    exact neg_injective hij
  have hdisj : Disjoint pos neg := by
    rw [Finset.disjoint_left]
    intro z hzPos hzNeg
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hzPos
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hzNeg
    have heq : (ts i : ℂ) = -(ts j : ℂ) := hi.trans hj.symm
    have hreal := congrArg Complex.re heq
    simp at hreal
    linarith [hpos i, hpos j]
  have hsumPos : (∑ a ∈ pos, a ^ q) =
      ∑ i : Fin 10, (ts i : ℂ) ^ q := by
    dsimp [pos]
    rw [Finset.sum_image (f := fun a : ℂ => a ^ q)
      (fun i _ j _ hij => hposInj hij)]
  have hsumNeg : (∑ a ∈ neg, a ^ q) =
      ∑ i : Fin 10, (-(ts i : ℂ)) ^ q := by
    dsimp [neg]
    rw [Finset.sum_image (f := fun a : ℂ => a ^ q)
      (fun i _ j _ hij => hnegInj hij)]
  have hnegPower (i : Fin 10) : (-(ts i : ℂ)) ^ q = (ts i : ℂ) ^ q := by
    rw [hq, show -(ts i : ℂ) = (-1 : ℂ) * (ts i : ℂ) by ring, mul_zpow]
    have hq' : -((2 * n + 2 : ℕ) : ℤ) =
        (-2 : ℤ) * ((n + 1 : ℕ) : ℤ) := by omega
    rw [hq']
    rw [zpow_mul]
    norm_num
  have hsumRoots :
      (∑ a ∈ contour51SignedTenRoots ts, a ^ q) =
        2 * ∑ i : Fin 10, (ts i : ℂ) ^ q := by
    change (∑ a ∈ pos ∪ neg, a ^ q) = _
    rw [Finset.sum_union hdisj, hsumPos, hsumNeg]
    simp_rw [hnegPower]
    calc
      _ = ∑ i : Fin 10, ((ts i : ℂ) ^ q + (ts i : ℂ) ^ q) := by
        rw [← Finset.sum_add_distrib]
      _ = _ := by
        rw [Finset.sum_add_distrib]
        ring
  calc
    _ = (1 / 2 : ℂ) * ∑ a ∈ contour51SignedTenRoots ts, a ^ q := by
      simp [q]
    _ = ∑ i : Fin 10, (ts i : ℂ) ^ q := by
      rw [hsumRoots]
      ring
    _ = _ := by rw [hq]

/-- The C1 radius-51 classification supplies the exact twenty-root list needed by the generic
finite-correction theorem. This specializes the analytic gluing and Cauchy reduction to the
original completed characteristic, without defining that characteristic from its roots. -/
theorem exists_completedNative_contour51_corrected_log_derivative :
    ∃ ts : Fin 10 → ℝ, StrictMono ts ∧
      (∀ i : Fin 10, 0 < ts i ∧ ts i < 50) ∧
      (∀ i : Fin 10,
        ts i ∈ Set.Ioo (sigmaTenZeroBoxLower i) (sigmaTenZeroBoxUpper i)) ∧
      ∀ n : ℕ, ∃ G : ℂ → ℂ, DiffContOnCl ℂ G (ball (0 : ℂ) 51) ∧
        (2 * Real.pi * Complex.I : ℂ)⁻¹ •
          ∮ z in C(0, 51),
            (-deriv completedNativeCharacteristicContinuation z /
              ((2 : ℂ) * completedNativeCharacteristicContinuation z)) / z ^ (n + 1) =
            iteratedDeriv n G 0 / (n.factorial : ℂ) ∧
          iteratedDeriv n G 0 / (n.factorial : ℂ) =
            iteratedDeriv n
                (fun z => -deriv completedNativeCharacteristicContinuation z /
                  ((2 : ℂ) * completedNativeCharacteristicContinuation z)) 0 /
                (n.factorial : ℂ) -
              (1 / 2 : ℂ) *
                ∑ a ∈ contour51SignedTenRoots ts, a ^ (-1 - (n : ℤ)) := by
  classical
  obtain ⟨_, ts, _, hmono, hboxes, hroots, _, hsimple⟩ :=
    sigmaContour51_original_characteristic_roots
  let poles : Finset ℂ := contour51SignedTenRoots ts
  have hpos (i : Fin 10) : 0 < ts i :=
    lt_trans (sigmaTenZeroLower_pos i) (hboxes i).1.1
  have hlt50 (i : Fin 10) : ts i < 50 :=
    lt_trans (hboxes i).1.2 (sigmaTenZeroUpper_lt_fifty i)
  have hpoles (z : ℂ) : z ∈ poles ↔
      (∃ i : Fin 10, (ts i : ℂ) = z) ∨
        (∃ i : Fin 10, -(ts i : ℂ) = z) := by
    simp [poles, contour51SignedTenRoots]
  have hzeros (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) 51) :
      (completedNativeCharacteristicContinuation z = 0 ↔ z ∈ poles) := by
    have hnorm : ‖z‖ ≤ 51 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    constructor
    · intro hzero
      rcases (hroots z hnorm).mp hzero with ⟨i, hroot | hroot⟩
      · exact (hpoles z).2 (Or.inl ⟨i, hroot.symm⟩)
      · exact (hpoles z).2 (Or.inr ⟨i, hroot.symm⟩)
    · intro hmem
      rcases (hpoles z).1 hmem with (⟨i, hroot⟩ | ⟨i, hroot⟩)
      · exact (hroots z hnorm).mpr ⟨i, Or.inl hroot.symm⟩
      · exact (hroots z hnorm).mpr ⟨i, Or.inr hroot.symm⟩
  have hrootNorm (i : Fin 10) : ‖(ts i : ℂ)‖ = ts i := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hpos i)]
  have horder : ∀ a ∈ poles, analyticOrderAt
      completedNativeCharacteristicContinuation a = 1 := by
    intro a ha
    rcases (hpoles a).1 ha with (⟨i, hroot⟩ | ⟨i, hroot⟩)
    · have hnorm : ‖a‖ ≤ 51 := by
        rw [← hroot, hrootNorm]
        linarith [hlt50 i]
      have hzball : a ∈ closedBall (0 : ℂ) 51 := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm
      exact hsimple a ((hzeros a hzball).2 ha) hnorm
    · have hnorm : ‖a‖ ≤ 51 := by
        rw [← hroot, norm_neg, hrootNorm]
        linarith [hlt50 i]
      have hzball : a ∈ closedBall (0 : ℂ) 51 := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm
      exact hsimple a ((hzeros a hzball).2 ha) hnorm
  have hinside : ∀ a ∈ poles, ‖a‖ < 51 := by
    intro a ha
    rcases (hpoles a).1 ha with (⟨i, hroot⟩ | ⟨i, hroot⟩)
    · rw [← hroot, hrootNorm]
      exact lt_trans (hlt50 i) (by norm_num)
    · rw [← hroot, norm_neg, hrootNorm]
      exact lt_trans (hlt50 i) (by norm_num)
  have hFzero : completedNativeCharacteristicContinuation 0 ≠ 0 := by
    intro hzero
    rcases (hroots 0 (by norm_num : ‖(0 : ℂ)‖ ≤ 51)).mp hzero with
      ⟨i, hroot | hroot⟩
    · have hreal := congrArg Complex.re hroot
      norm_num at hreal
      linarith [hpos i]
    · have hreal := congrArg Complex.re hroot
      norm_num at hreal
      linarith [hpos i]
  refine ⟨ts, hmono, (fun i => ⟨hpos i, hlt50 i⟩), (fun i => (hboxes i).1), ?_⟩
  intro n
  simpa [poles, contour51SignedTenRoots] using exists_contour51_corrected_log_derivative
    completedNativeCharacteristicContinuation poles n
    completedNativeCharacteristicContinuation_analyticAt
    hzeros horder hinside hFzero

/-- The completed radius-51 contour identity in the original source normalization. For the
kernel of order `2*n+2`, the contour coefficient is the original central sigma jet minus the
sum of the ten positive real modes certified by C1. -/
theorem completedNative_contour51_jet_residue_identity :
    ∃ ts : Fin 10 → ℝ, StrictMono ts ∧
      (∀ i : Fin 10, 0 < ts i ∧ ts i < 50) ∧
      (∀ i : Fin 10,
        ts i ∈ Set.Ioo (sigmaTenZeroBoxLower i) (sigmaTenZeroBoxUpper i)) ∧
      ∀ n : ℕ,
      ∃ G : ℂ → ℂ, DiffContOnCl ℂ G (ball (0 : ℂ) 51) ∧
        (2 * Real.pi * Complex.I : ℂ)⁻¹ •
          ∮ z in C(0, 51),
            (-deriv completedNativeCharacteristicContinuation z /
              ((2 : ℂ) * completedNativeCharacteristicContinuation z)) /
                z ^ (2 * n + 2) =
          (CarrySigmaSource.completedSigmaLogJet 0 n : ℂ) -
            ∑ i : Fin 10,
              (ts i : ℂ) ^ (-((2 * n + 2 : ℕ) : ℤ)) := by
  obtain ⟨ts, hmono, hbounds, hheightboxes, hforall⟩ :=
    exists_completedNative_contour51_corrected_log_derivative
  refine ⟨ts, hmono, hbounds, hheightboxes, ?_⟩
  intro n
  obtain ⟨G, hG, hcontour, hcoeff⟩ := hforall (2 * n + 1)
  have hdomain : completedNativeHeightDomain ∈ 𝓝 (0 : ℂ) :=
    isOpen_completedNativeHeightDomain.mem_nhds zero_mem_completedNativeHeightDomain
  have hsourceNear : completedNativeCharacteristicContinuation =ᶠ[𝓝 (0 : ℂ)]
      completedNativeOperatorCharacteristic := by
    filter_upwards [hdomain] with z hz
    exact completedNativeCharacteristicContinuation_eq_native
      (by simpa [completedNativeHeightDomain] using hz)
  have hsourceDerivNear : deriv completedNativeCharacteristicContinuation =ᶠ[𝓝 (0 : ℂ)]
      deriv completedNativeOperatorCharacteristic := hsourceNear.deriv
  have hresponseNear :
      (fun z : ℂ => -deriv completedNativeCharacteristicContinuation z /
          ((2 : ℂ) * completedNativeCharacteristicContinuation z)) =ᶠ[𝓝 (0 : ℂ)]
        completedNativeLogResponse := by
    filter_upwards [hsourceNear, hsourceDerivNear] with z hsource hderiv
    simp only [completedNativeLogResponse]
    rw [hderiv, hsource]
  have hresponseIter := hresponseNear.iteratedDeriv_eq (2 * n + 1)
  have hnativeResponseEq : completedNativeLogResponse =
      CarrySelfAdjointOperator.completedGreenNormalizedResponse
        CarrySelfAdjointOperator.completedNativeOperatorCharacteristic
        CarrySelfAdjointOperator.completedNativeOperatorBoundaryCompanion := by
    funext z
    unfold completedNativeLogResponse CarrySelfAdjointOperator.completedGreenNormalizedResponse
    rw [CarrySelfAdjointOperator.completedNativeOperatorBoundaryCompanion_eq_neg_deriv z]
  have hnativeJet :
      iteratedDeriv (2 * n + 1) completedNativeLogResponse 0 /
          ((2 * n + 1).factorial : ℂ) =
        (CarrySigmaSource.completedSigmaLogJet 0 n : ℂ) := by
    calc
      _ = (CarrySelfAdjointOperator.canonicalCompletedNativeLogDerivativeMoment n : ℂ) := by
        rw [hnativeResponseEq]
        change CarrySelfAdjointOperator.completedNativeGreenResponseTaylorCoefficient
          (2 * n + 1) = _
        exact CarrySelfAdjointOperator.completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical n
      _ = (CarrySigmaSource.completedSigmaLogJet 0 n : ℂ) := by
        rw [← CarrySigmaSource.sigma_log_jet_center_eq_canonical n]
  have hresponseJet :
      iteratedDeriv (2 * n + 1)
          (fun z : ℂ => -deriv completedNativeCharacteristicContinuation z /
            ((2 : ℂ) * completedNativeCharacteristicContinuation z)) 0 /
          ((2 * n + 1).factorial : ℂ) =
        (CarrySigmaSource.completedSigmaLogJet 0 n : ℂ) := by
    rw [hresponseIter]
    exact hnativeJet
  refine ⟨G, hG, ?_⟩
  calc
    _ = iteratedDeriv (2 * n + 1) G 0 / ((2 * n + 1).factorial : ℂ) := hcontour
    _ = iteratedDeriv (2 * n + 1)
          (fun z : ℂ => -deriv completedNativeCharacteristicContinuation z /
            ((2 : ℂ) * completedNativeCharacteristicContinuation z)) 0 /
          ((2 * n + 1).factorial : ℂ) -
        (1 / 2 : ℂ) *
          ∑ a ∈ contour51SignedTenRoots ts,
            a ^ (-1 - ((2 * n + 1 : ℕ) : ℤ)) := hcoeff
    _ = _ := by
      rw [hresponseJet, contour51_signed_ten_root_power_sum ts hmono
        (fun i => (hbounds i).1) n]

#print axioms contour51_pole_kernel_integrable_and_integral_zero
#print axioms contour51_cauchy_reduction_of_finite_correction
#print axioms exists_contour51_corrected_log_derivative
#print axioms exists_completedNative_contour51_corrected_log_derivative
#print axioms completedNative_contour51_jet_residue_identity

end
end CarrySigmaObstruction
