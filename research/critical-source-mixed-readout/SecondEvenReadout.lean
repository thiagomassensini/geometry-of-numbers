import SourceCoordinates
import CarrySelfAdjointOperator.CompletedNativeChiralReturnBoundaryCoefficientProvenance

namespace CarryCriticalMixed
open CarrySelfAdjointOperator CarrySelfAdjointOperator.ChiralReturn CarryCriticalRelative
open Filter Topology
open scoped BigOperators ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192

def secondEvenJet (a : ℝ) : Fin 4 → ℂ := ![(a:ℂ),0,-1,0]
def secondStencil (a : ℝ) (k : ℕ) : Fin 4 → ℂ :=
  ![(a:ℂ)-(((k:ℝ)+1:ℝ):ℂ)^2/2, (((k:ℝ)+1:ℝ):ℂ)^2,
    -(((k:ℝ)+1:ℝ):ℂ)^2/2, 0]
def secondBalance (a : ℝ) (k : ℕ) : ℝ :=
  (storage k (nativeSourceChiralJetInput 2 k (secondEvenJet a)) 1).re

theorem second_stencil_exact (a : ℝ) (k : ℕ) :
    jetStencil 2 k (secondEvenJet a) = secondStencil a k := by
  have hk : ((k:ℂ)+1) ≠ 0 := by
    exact_mod_cast (show (k:ℝ)+1 ≠ 0 by positivity)
  funext r
  fin_cases r
  all_goals
    norm_num [jetStencil, secondEvenJet, secondStencil, Fin.sum_univ_succ,
      nativeSourceJetOrderPhase, completedGreenForwardWeight, step,
      canonicalCompletedC3RadialSecondStep, canonicalCompletedC3RadialTiltStep,
      canonicalGreenJetStep, Complex.I_sq]
  all_goals field_simp
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq]
  all_goals ring

/-- Three nonzero sample coefficients are forced by the original four-jet
source. The fourth is exactly zero, not a discarded independent channel. -/
theorem second_balance_three_slopes (a : ℝ) (k : ℕ)
    (hF : ∀ r : Fin 4, completedNativeOperatorCharacteristic
      (canonicalCompletedC3RadialTiltPoint k r) ≠ 0)
    (hP : ∀ r : Fin 4, completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k r) ≠ 0) :
    secondBalance a k = ((k:ℝ)+1) *
      ((a^2-7*a*((k:ℝ)+1)^2/12+((k:ℝ)+1)^4/24) * (radialCompletedSlope k 0).re +
       (2*a*((k:ℝ)+1)^2/3-((k:ℝ)+1)^4/30) * (radialCompletedSlope k 1).re +
       (-a*((k:ℝ)+1)^2/4+((k:ℝ)+1)^4/120) * (radialCompletedSlope k 2).re) := by
  rw [secondBalance, storage_eq_stencil_slope 2 k _ hF hP, second_stencil_exact]
  simp only [secondStencil, radialIncidentSynthesis, LinearMap.coe_mk, AddHom.coe_mk,
    Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero, zero_mul,
    zero_smul, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right,
    inner_completedNativeRadialChiralCauchyState]
  push_cast
  norm_num [map_ofNat, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, pow_two]
  ring

abbrev sourceCoefficient := nativeSourceOddBoundaryCoefficient

def balanceConstant (a : ℝ) : ℝ :=
  sourceCoefficient 0*a^2+2*sourceCoefficient 1*a+sourceCoefficient 2

def balanceCorrection (a : ℝ) : ℝ :=
  -sourceCoefficient 1*a^2-40*sourceCoefficient 2*a-14*sourceCoefficient 3

def balanceFourth (a : ℝ) : ℝ := sourceCoefficient 2*a^2+462*sourceCoefficient 3*a

def normalizedSourceRemainder (R : ℂ → ℂ) (a t : ℝ) : ℝ :=
  (a^2*t^4-7*a*t^2/12+1/24)*(R (t:ℂ)).re +
  256*(2*a*t^2/3-1/30)*(R ((2*t:ℝ):ℂ)).re +
  6561*(-a*t^2/4+1/120)*(R ((3*t:ℝ):ℂ)).re

/-- This is the full original source, not its polynomial truncation.
The analytic remainder is retained in the same scalar balance. -/
theorem second_balance_exact_source_remainder :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧ ∀ a : ℝ, ∀ᶠ k : ℕ in atTop,
      secondBalance a k = balanceConstant a +
        (canonicalGreenJetRealStep k)^2*balanceCorrection a +
        (canonicalGreenJetRealStep k)^4*balanceFourth a -
        (canonicalGreenJetRealStep k)^6*sourceCoefficient 3*a^2 +
        (canonicalGreenJetRealStep k)^3 *
          normalizedSourceRemainder R a (canonicalGreenJetRealStep k) := by
  obtain ⟨R,hRa,hR⟩ := nativeSourceTransverseSlope_exact_remainder
  refine ⟨R,hRa,?_⟩
  intro a
  have ht (j : ℕ) : Tendsto (fun k => (((j+1:ℕ):ℂ) *
      (canonicalGreenJetRealStep k : ℂ))) atTop (nhds 0) := by
    have hs : Tendsto (fun k => (canonicalGreenJetRealStep k : ℂ)) atTop (nhds 0) := by
      simpa only [canonicalGreenJetRealStep_coe] using canonicalGreenJetStep_tendsto_zero
    simpa only [mul_zero] using hs.const_mul (((j+1:ℕ):ℂ))
  filter_upwards [(ht 0).eventually hR, (ht 1).eventually hR, (ht 2).eventually hR,
    canonicalCompletedNativeRadialProjectiveChiral_eventually_regular 4] with k h0 h1 h2 hreg
  rw [second_balance_three_slopes a k (fun r => (hreg r).2.1) (fun r => (hreg r).2.2)]
  have hpoint (j : ℕ) : canonicalCompletedC3RadialTiltPoint k j =
      Complex.I * (((j+1:ℕ):ℂ) * (canonicalGreenJetRealStep k : ℂ)) := by
    unfold canonicalCompletedC3RadialTiltPoint canonicalCompletedC3RadialTiltStep
    rw [← canonicalGreenJetRealStep_coe]
    ring
  have hs0 := congrArg Complex.re h0
  have hs1 := congrArg Complex.re h1
  have hs2 := congrArg Complex.re h2
  simp only [radialCompletedSlope, hpoint]
  rw [hs0,hs1,hs2]
  simp only [← Complex.ofReal_natCast, ← Complex.ofReal_mul]
  simp only [Complex.re_sum, Complex.add_re, ← Complex.ofReal_pow,
    Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero]
  norm_num [Finset.sum_range_succ]
  unfold balanceConstant balanceCorrection balanceFourth normalizedSourceRemainder
    canonicalGreenJetRealStep
  simp only [canonicalGreenJetStep, ← Complex.ofReal_natCast, ← Complex.ofReal_add,
    ← Complex.ofReal_one, ← Complex.ofReal_inv]
  generalize hK : (k:ℝ)+1 = K
  have hk : K ≠ 0 := by rw [← hK]; positivity
  ring_nf
  field_simp
  push_cast
  ring

end
end CarryCriticalMixed
