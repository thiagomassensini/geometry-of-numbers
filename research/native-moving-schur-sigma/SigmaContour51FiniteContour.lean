import SigmaContour51Residue

/-!
# The circle integral of an interior simple-pole kernel

The logarithmic-derivative residue calculation reduces the global contour identity to Cauchy's
formula plus the integral of `(z - a)⁻¹ z^(-k)`. This module proves that this integral is zero
for every positive integer `k`, using Mathlib's circle-integral formulas for inverse powers.
-/

namespace CarrySigmaObstruction

open Complex Set Metric

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

#print axioms contour51_pole_kernel_integrable_and_integral_zero

end
end CarrySigmaObstruction
