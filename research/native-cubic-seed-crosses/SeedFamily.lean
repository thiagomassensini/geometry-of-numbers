import SeedSigns

namespace CarryCubicSeed
open CarrySelfAdjointOperator NativeLaguerre CarryCriticalTfvd CarryCurvatureGreen
open CarryQuarticBoundary CarryCubicTfvd CarryCubicQuartic
open scoped InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The SAME two-profile coefficient, before adding the original seed. -/
def twoJetCubic (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (a : ℝ) : ℝ :=
  (cubicKernel eta h0 h1 (fourthShape-(a : ℂ) • curvatureInput)
    (fourthShape-(a : ℂ) • curvatureInput)).re

/-- The original nine-pair coefficient; a,b stay free, not fitted to moments. -/
def nativeCubicFamily (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (a b : ℝ) : ℝ :=
  (cubicKernel eta h0 h1
    (fourthShape-(a : ℂ) • curvatureInput-(b : ℂ) • Finsupp.single 0 1)
    (fourthShape-(a : ℂ) • curvatureInput-(b : ℂ) • Finsupp.single 0 1)).re

/-- Abbreviation for the proved ordered crosses, without changing any kernel. -/
def seedPenalty (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (a : ℝ) : ℝ :=
  (cubicKernel eta h0 h1 fourthShape (Finsupp.single 0 1)+
    cubicKernel eta h0 h1 (Finsupp.single 0 1) fourthShape).re-
    a*(cubicKernel eta h0 h1 curvatureInput (Finsupp.single 0 1)+
      cubicKernel eta h0 h1 (Finsupp.single 0 1) curvatureInput).re

theorem two_jet_cubic_lower (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (a : ℝ) (ha : 0 ≤ a) :
    (3/17920 : ℝ)+a^2/20+23*a/2240 ≤ twoJetCubic eta h0 h1 a :=
  two_jet_cone_lower eta h0 h1 a ha

theorem seed_penalty_lower (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (a : ℝ) (ha : 0 ≤ a) :
    (1/72 : ℝ)+a/24 ≤ seedPenalty eta h0 h1 a := by
  have h4 := native_quartic_seed_sum_lower eta h0 h1
  have h2 := mul_le_mul_of_nonneg_left (native_quadratic_seed_sum_upper eta h0 h1) ha
  unfold seedPenalty
  linarith

/-- All nine original ordered pairings reduce to a physical seed quadratic.
This is an identity, not a positivity premise or a new moment functional. -/
theorem native_family_exact (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (a b : ℝ) :
    nativeCubicFamily eta h0 h1 a b = twoJetCubic eta h0 h1 a-
      b*seedPenalty eta h0 h1 a-
      7*eta^2*‖baseGradient eta h0 h1 (completedNativeChiralCauchyFeature 0)‖^2*b^2 := by
  unfold nativeCubicFamily twoJetCubic seedPenalty
  rw [cubic_three_input_expansion, two_jet_expansion, native_seed_seed]
  simp only [nativeQuarticU3, nativeU3, spatialU, cubicKernel,
    mixedQuarticQuadratic, mixedQuadraticQuartic, Complex.add_re]
  ring

theorem native_family_at_zero (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (a : ℝ) :
    nativeCubicFamily eta h0 h1 a 0=twoJetCubic eta h0 h1 a := by
  rw [native_family_exact]
  ring

/-- An explicit residual inequality after the independent physical identities. -/
theorem native_family_positive_iff (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (a b : ℝ) :
    0 < nativeCubicFamily eta h0 h1 a b ↔
      b*seedPenalty eta h0 h1 a+
        7*eta^2*‖baseGradient eta h0 h1 (completedNativeChiralCauchyFeature 0)‖^2*b^2 <
          twoJetCubic eta h0 h1 a := by
  rw [native_family_exact]
  constructor <;> intro hh <;> linarith

/-- For a≥0 the coefficient decreases strictly with nonnegative seed amplitude.
This says nothing about the actual moment-selected values of a,b. -/
theorem native_family_strict_decrease (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (a x y : ℝ) (ha : 0 ≤ a) (hx : 0 ≤ x) (hxy : x < y) :
    nativeCubicFamily eta h0 h1 a y < nativeCubicFamily eta h0 h1 a x := by
  have hp := seed_penalty_lower eta h0 h1 a ha
  have hpp : 0 < seedPenalty eta h0 h1 a := by linarith
  have hm := mul_lt_mul_of_pos_right hxy hpp
  have hs : x^2 ≤ y^2 := by nlinarith
  have hn := mul_le_mul_of_nonneg_left hs
    (by positivity : 0 ≤ 7*eta^2*‖baseGradient eta h0 h1 (completedNativeChiralCauchyFeature 0)‖^2)
  rw [native_family_exact, native_family_exact]
  nlinarith

/-- A concrete negative source in this SAME family. This is a no-go only for
universal positivity with free seed coefficient, not for the canonical residual. -/
theorem native_family_negative_witness (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (a : ℝ) (ha : 0 ≤ a) :
    nativeCubicFamily eta h0 h1 a (72*(twoJetCubic eta h0 h1 a+1)) ≤ -1 := by
  have hA := two_jet_cubic_lower eta h0 h1 a ha
  have hA0 : 0 ≤ twoJetCubic eta h0 h1 a := by nlinarith [sq_nonneg a]
  have hb : 0 ≤ 72*(twoJetCubic eta h0 h1 a+1) := by linarith
  have hP := seed_penalty_lower eta h0 h1 a ha
  have hP0 : (1/72 : ℝ) ≤ seedPenalty eta h0 h1 a := by linarith
  have hm := mul_le_mul_of_nonneg_left hP0 hb
  have hn : 0 ≤ 7*eta^2*‖baseGradient eta h0 h1 (completedNativeChiralCauchyFeature 0)‖^2*
      (72*(twoJetCubic eta h0 h1 a+1))^2 := by positivity
  rw [native_family_exact]
  nlinarith

theorem exists_positive_seed_negative_family (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (a : ℝ) (ha : 0 ≤ a) :
    ∃ b : ℝ, 0 < b ∧ nativeCubicFamily eta h0 h1 a b < 0 := by
  refine ⟨72*(twoJetCubic eta h0 h1 a+1), ?_, ?_⟩
  · have hh := two_jet_cubic_lower eta h0 h1 a ha
    nlinarith [sq_nonneg a]
  · exact lt_of_le_of_lt (native_family_negative_witness eta h0 h1 a ha) (by norm_num)

end
end CarryCubicSeed
