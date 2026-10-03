import GeometryOfNumbers.Analysis.C2FiberRealDynamics
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Quadratic mass of a real deformed C2 branch orbit

This sigma-family is a downstream radial comparison family. It does not
define or select the existing critical amplitude. Its half specialization
is identified with the preexisting center step.

Historical reference: formalizacao_C2, dc35555879e3c0f188508c729c4a0ea31be246fb,
LeanC2/Operators/BranchBarrier.lean. Only its real weight, shifted mass
expression and scalar barrier are recovered. No historical module is imported.
The two directions count signed C2 branches; their physical leg angles are
not asserted to coincide. Quadratic invariance forgets angular defects.
-/

namespace GeometryOfNumbers.Analysis

noncomputable section

/-- Under odd core, the C2 center divisible by four begins exactly at depth two. -/
theorem c2BranchDepth_ge_two_iff_center_four_dvd (m k : ℕ) (hm : Odd m) :
    4 ∣ 2 ^ k * m ↔ 2 ≤ k := by
  cases k with
  | zero =>
    simp only [pow_zero, one_mul]
    constructor
    · rintro ⟨z, hz⟩
      rcases hm with ⟨r, hr⟩
      omega
    · intro h
      omega
  | succ k =>
    cases k with
    | zero =>
      change 4 ∣ 2 * m ↔ 2 ≤ 1
      constructor
      · rintro ⟨z, hz⟩
        rcases hm with ⟨r, hr⟩
        omega
      · intro h
        omega
    | succ k =>
      constructor
      · intro _
        omega
      · intro _
        refine ⟨2 ^ k * m, ?_⟩
        simp only [pow_succ]
        ring

theorem c2BranchDirections_distinct (m k : ℕ) :
    c2FiberPoint m (-1) k ≠ c2FiberPoint m 1 k := by
  unfold c2FiberPoint
  intro h
  linarith

theorem c2BranchDirections_card (m k : ℕ) :
    ({c2FiberPoint m (-1) k, c2FiberPoint m 1 k} : Finset ℝ).card = 2 := by
  classical
  exact Finset.card_pair (c2BranchDirections_distinct m k)

def c2RadialAmplitudeRatio (sigma : ℝ) : ℝ :=
  (2 : ℝ) ^ (-sigma)

def c2RadialEnergyRatio (sigma : ℝ) : ℝ :=
  c2RadialAmplitudeRatio sigma ^ 2

theorem c2RadialEnergyRatio_eq_rpow (sigma : ℝ) :
    c2RadialEnergyRatio sigma = (2 : ℝ) ^ (-2 * sigma) := by
  unfold c2RadialEnergyRatio c2RadialAmplitudeRatio
  rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

theorem c2RadialEnergyRatio_pos (sigma : ℝ) :
    0 < c2RadialEnergyRatio sigma := by
  rw [c2RadialEnergyRatio_eq_rpow]
  exact Real.rpow_pos_of_pos (by norm_num) _

theorem c2RadialEnergyRatio_lt_one (sigma : ℝ) (hsigma : 0 < sigma) :
    c2RadialEnergyRatio sigma < 1 := by
  rw [c2RadialEnergyRatio_eq_rpow]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)

def c2DeformedFiberStep (sigma t : ℝ) (v : RealPlaneState) : RealPlaneState :=
  scaleRealPlane (c2RadialAmplitudeRatio sigma)
    (rotateRealPlane (-t * Real.log 2) v)

theorem c2DeformedFiberStep_energy (sigma t : ℝ) (v : RealPlaneState) :
    realPlaneEnergy (c2DeformedFiberStep sigma t v) =
      c2RadialEnergyRatio sigma * realPlaneEnergy v := by
  rw [c2DeformedFiberStep, scaleRealPlane_energy, rotateRealPlane_energy]
  rfl

theorem c2DeformedFiberStep_energy_independent_time
    (sigma t₁ t₂ : ℝ) (v : RealPlaneState) :
    realPlaneEnergy (c2DeformedFiberStep sigma t₁ v) =
      realPlaneEnergy (c2DeformedFiberStep sigma t₂ v) := by
  rw [c2DeformedFiberStep_energy, c2DeformedFiberStep_energy]

theorem c2DeformedFiberStep_iterate_energy
    (sigma t : ℝ) (k : ℕ) (v : RealPlaneState) :
    realPlaneEnergy ((c2DeformedFiberStep sigma t)^[k] v) =
      c2RadialEnergyRatio sigma ^ k * realPlaneEnergy v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', c2DeformedFiberStep_energy, ih, pow_succ]
    ring

theorem c2DeformedUnitOrbit_energy (sigma t : ℝ) (k : ℕ) :
    realPlaneEnergy ((c2DeformedFiberStep sigma t)^[k]
      (realCriticalDepthSeed 2 0 (by decide))) = c2RadialEnergyRatio sigma ^ k := by
  rw [c2DeformedFiberStep_iterate_energy, realCriticalDepthSeed_energy,
    realDepthMass_zero, mul_one]

theorem c2RadialAmplitudeRatio_half :
    c2RadialAmplitudeRatio ((1 : ℝ) / 2) = (2 : ℝ) ^ (-(1 : ℝ) / 2) := by
  unfold c2RadialAmplitudeRatio
  congr 1
  ring

theorem c2RadialEnergyRatio_half :
    c2RadialEnergyRatio ((1 : ℝ) / 2) = (1 : ℝ) / 2 := by
  rw [c2RadialEnergyRatio_eq_rpow]
  have h : -2 * ((1 : ℝ) / 2) = (-1 : ℝ) := by ring
  rw [h, Real.rpow_neg_one]
  norm_num

theorem c2DeformedFiberStep_half_eq_c2CenterFiberStep (t : ℝ) :
    c2DeformedFiberStep ((1 : ℝ) / 2) t = c2CenterFiberStep t := by
  funext v
  unfold c2DeformedFiberStep c2CenterFiberStep
  simp only [c2RadialAmplitudeRatio_half, criticalVerticalAmplitudeRatio_eq_rpow,
    Nat.cast_ofNat]

/-- Two signed branch directions, first admitted center depth two.
The time parameter remains in the actual real orbit until energy is taken. -/
def c2BranchOrbitMass (sigma t : ℝ) : ℝ :=
  2 * ∑' j : ℕ, realPlaneEnergy ((c2DeformedFiberStep sigma t)^[j + 2]
    (realCriticalDepthSeed 2 0 (by decide)))

theorem c2BranchOrbitMass_eq_geometric_series (sigma t : ℝ) :
    c2BranchOrbitMass sigma t = 2 * ∑' j : ℕ, c2RadialEnergyRatio sigma ^ (j + 2) := by
  unfold c2BranchOrbitMass
  simp only [c2DeformedUnitOrbit_energy]

theorem c2BranchOrbitMass_independent_time (sigma t₁ t₂ : ℝ) :
    c2BranchOrbitMass sigma t₁ = c2BranchOrbitMass sigma t₂ := by
  rw [c2BranchOrbitMass_eq_geometric_series, c2BranchOrbitMass_eq_geometric_series]

/-- Literal local copy of the legacy real branch weight; comparison only. -/
def legacyC2BranchWeight (sigma : ℝ) : ℝ :=
  (2 : ℝ) ^ (-2 * sigma)

/-- Literal local copy of the legacy shifted two-direction real mass. -/
def legacyC2BranchNormSq (sigma : ℝ) : ℝ :=
  2 * ∑' j : ℕ, legacyC2BranchWeight sigma ^ (j + 2)

theorem c2RadialEnergyRatio_eq_legacyBranchWeight (sigma : ℝ) :
    c2RadialEnergyRatio sigma = legacyC2BranchWeight sigma :=
  c2RadialEnergyRatio_eq_rpow sigma

theorem c2BranchOrbitMass_eq_legacyBranchNormSq (sigma t : ℝ) :
    c2BranchOrbitMass sigma t = legacyC2BranchNormSq sigma := by
  rw [c2BranchOrbitMass_eq_geometric_series]
  simp only [legacyC2BranchNormSq, c2RadialEnergyRatio_eq_legacyBranchWeight]

theorem c2BranchUnitOrbitEnergy_summable (sigma t : ℝ) (hsigma : 0 < sigma) :
    Summable (fun j : ℕ => realPlaneEnergy ((c2DeformedFiberStep sigma t)^[j + 2]
      (realCriticalDepthSeed 2 0 (by decide)))) := by
  simp only [c2DeformedUnitOrbit_energy]
  have h := summable_geometric_of_lt_one (c2RadialEnergyRatio_pos sigma).le
    (c2RadialEnergyRatio_lt_one sigma hsigma)
  simpa only [pow_add] using h.mul_right (c2RadialEnergyRatio sigma ^ 2)

theorem c2BranchOrbitMass_closed_form (sigma t : ℝ) (hsigma : 0 < sigma) :
    c2BranchOrbitMass sigma t =
      2 * c2RadialEnergyRatio sigma ^ 2 / (1 - c2RadialEnergyRatio sigma) := by
  rw [c2BranchOrbitMass_eq_geometric_series]
  simp_rw [pow_add]
  rw [tsum_mul_right, tsum_geometric_of_lt_one (c2RadialEnergyRatio_pos sigma).le
    (c2RadialEnergyRatio_lt_one sigma hsigma)]
  ring

theorem c2BranchOrbitMass_half (t : ℝ) :
    c2BranchOrbitMass ((1 : ℝ) / 2) t = 1 := by
  rw [c2BranchOrbitMass_closed_form _ _ (by norm_num), c2RadialEnergyRatio_half]
  norm_num

private theorem radialEnergyRatio_lt_half {sigma : ℝ} (hsigma : (1 : ℝ) / 2 < sigma) :
    c2RadialEnergyRatio sigma < (1 : ℝ) / 2 := by
  rw [c2RadialEnergyRatio_eq_rpow]
  have h := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : 1 < (2 : ℝ))
    (by linarith : -2 * sigma < (-1 : ℝ))
  simpa [Real.rpow_neg_one] using h

private theorem half_lt_radialEnergyRatio {sigma : ℝ} (hsigma : sigma < (1 : ℝ) / 2) :
    (1 : ℝ) / 2 < c2RadialEnergyRatio sigma := by
  rw [c2RadialEnergyRatio_eq_rpow]
  have h := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : 1 < (2 : ℝ))
    (by linarith : (-1 : ℝ) < -2 * sigma)
  simpa [Real.rpow_neg_one] using h

private theorem mass_lt_one {sigma : ℝ} (t : ℝ) (hsigma : (1 : ℝ) / 2 < sigma) :
    c2BranchOrbitMass sigma t < 1 := by
  have hsigma0 : 0 < sigma := by linarith
  have hq0 := (c2RadialEnergyRatio_pos sigma).le
  have hqhalf := radialEnergyRatio_lt_half hsigma
  have hden := sub_pos.mpr (c2RadialEnergyRatio_lt_one sigma hsigma0)
  rw [c2BranchOrbitMass_closed_form sigma t hsigma0]
  apply (div_lt_one hden).2
  nlinarith

private theorem one_lt_mass {sigma : ℝ} (t : ℝ) (hsigma0 : 0 < sigma)
    (hsigma : sigma < (1 : ℝ) / 2) : 1 < c2BranchOrbitMass sigma t := by
  have hq0 := (c2RadialEnergyRatio_pos sigma).le
  have hqhalf := half_lt_radialEnergyRatio hsigma
  have hden := sub_pos.mpr (c2RadialEnergyRatio_lt_one sigma hsigma0)
  rw [c2BranchOrbitMass_closed_form sigma t hsigma0]
  apply (one_lt_div hden).2
  nlinarith

theorem c2BranchOrbitMass_eq_one_iff (sigma t : ℝ) (hsigma : 0 < sigma) :
    c2BranchOrbitMass sigma t = 1 ↔ sigma = (1 : ℝ) / 2 := by
  constructor
  · intro heq
    rcases lt_trichotomy sigma ((1 : ℝ) / 2) with hleft | hhalf | hright
    · have hgt := one_lt_mass t hsigma hleft
      linarith
    · exact hhalf
    · have hlt := mass_lt_one t hright
      linarith
  · intro hhalf
    subst sigma
    exact c2BranchOrbitMass_half t

theorem c2BranchOrbitMass_lt_one_iff (sigma t : ℝ) (hsigma : 0 < sigma) :
    c2BranchOrbitMass sigma t < 1 ↔ (1 : ℝ) / 2 < sigma := by
  constructor
  · intro hlt
    rcases lt_trichotomy sigma ((1 : ℝ) / 2) with hleft | hhalf | hright
    · have hgt := one_lt_mass t hsigma hleft
      linarith
    · subst sigma
      rw [c2BranchOrbitMass_half] at hlt
      linarith
    · exact hright
  · intro hright
    exact mass_lt_one t hright

theorem c2BranchOrbitMass_gt_one_iff (sigma t : ℝ) (hsigma : 0 < sigma) :
    1 < c2BranchOrbitMass sigma t ↔ sigma < (1 : ℝ) / 2 := by
  constructor
  · intro hgt
    rcases lt_trichotomy sigma ((1 : ℝ) / 2) with hleft | hhalf | hright
    · exact hleft
    · subst sigma
      rw [c2BranchOrbitMass_half] at hgt
      linarith
    · have hlt := mass_lt_one t hright
      linarith
  · intro hleft
    exact one_lt_mass t hsigma hleft

end

end GeometryOfNumbers.Analysis
