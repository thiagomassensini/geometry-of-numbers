import SourceTaylor
import SecondEvenLimit

namespace CarrySourceLaw
open CarrySelfAdjointOperator CarrySelfAdjointOperator.ChiralReturn
open CarryCriticalMixed CarryCriticalRelative Filter Topology
open scoped BigOperators ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

abbrev h := canonicalCompletedNativeLogDerivativeMoment

def oddJet (a : ℝ) : Fin 4 → ℂ := ![0,(a:ℂ),0,-1]
def oddStencil (a : ℝ) (k : ℕ) : Fin 4 → ℂ :=
  let K : ℂ := ((k:ℝ)+1 : ℝ)
  ![Complex.I*(a*K-K^3/6), Complex.I*(-a*K+K^3/2),
    Complex.I*(-K^3/2), Complex.I*(K^3/6)]
def oddBalance (a : ℝ) (k : ℕ) : ℝ :=
  (storage k (nativeSourceChiralJetInput 2 k (oddJet a)) 1).re

theorem odd_stencil_exact (a : ℝ) (k : ℕ) :
    jetStencil 2 k (oddJet a) = oddStencil a k := by
  have hk : ((k:ℂ)+1) ≠ 0 := by
    exact_mod_cast (show (k:ℝ)+1 ≠ 0 by positivity)
  funext r
  fin_cases r
  all_goals
    norm_num [jetStencil, oddJet, oddStencil, Fin.sum_univ_succ,
      nativeSourceJetOrderPhase, completedGreenForwardWeight, step,
      canonicalCompletedC3RadialSecondStep, canonicalCompletedC3RadialTiltStep,
      canonicalGreenJetStep, Complex.I_sq]
  all_goals field_simp
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq]

/-- Every Cauchy cross is computed before the scalar source expansion. -/
theorem odd_balance_four_slopes (a : ℝ) (k : ℕ)
    (hF : ∀ r : Fin 4, completedNativeOperatorCharacteristic
      (canonicalCompletedC3RadialTiltPoint k r) ≠ 0)
    (hP : ∀ r : Fin 4, completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k r) ≠ 0) :
    oddBalance a k = ((k:ℝ)+1) *
      ((((k:ℝ)+1)^6/360-13*((k:ℝ)+1)^4*a/180+((k:ℝ)+1)^2*a^2/3) *
        (radialCompletedSlope k 0).re +
       (-((k:ℝ)+1)^6/360+4*((k:ℝ)+1)^4*a/45-((k:ℝ)+1)^2*a^2/6) *
        (radialCompletedSlope k 1).re +
       (((k:ℝ)+1)^6/840-((k:ℝ)+1)^4*a/20) * (radialCompletedSlope k 2).re +
       (-((k:ℝ)+1)^6/5040+((k:ℝ)+1)^4*a/90) * (radialCompletedSlope k 3).re) := by
  rw [oddBalance, storage_eq_stencil_slope 2 k _ hF hP, odd_stencil_exact]
  simp only [oddStencil, radialIncidentSynthesis, LinearMap.coe_mk, AddHom.coe_mk,
    Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero, inner_add_left,
    inner_add_right, inner_smul_left, inner_smul_right,
    inner_completedNativeRadialChiralCauchyState]
  push_cast
  norm_num [map_ofNat, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im, pow_succ]
  ring

def oddConstant (a : ℝ) : ℝ := 2*h 1*a^2+4*h 2*a+2*h 3
def oddCorrection (a : ℝ) : ℝ := -10*h 2*a^2-168*h 3*a-60*h 4

def oddHigher (a t : ℝ) : ℝ :=
  42*h 3*a^2 + 3948*h 4*a - 170*t^2*h 4*a^2

def oddRemainder (R : ℂ → ℂ) (a t : ℝ) : ℝ :=
  (1/360-13*a*t^2/180+a^2*t^4/3)*(R (t:ℂ)).re +
  1024*(-1/360+4*a*t^2/45-a^2*t^4/6)*(R ((2*t:ℝ):ℂ)).re +
  59049*(1/840-a*t^2/20)*(R ((3*t:ℝ):ℂ)).re +
  1048576*(-1/5040+a*t^2/90)*(R ((4*t:ℝ):ℂ)).re

theorem odd_balance_exact_remainder :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧ ∀ a : ℝ, ∀ᶠ k : ℕ in atTop,
      oddBalance a k = oddConstant a + canonicalGreenJetRealStep k^2*oddCorrection a +
        canonicalGreenJetRealStep k^4*oddHigher a (canonicalGreenJetRealStep k) +
        canonicalGreenJetRealStep k^3*oddRemainder R a (canonicalGreenJetRealStep k) := by
  obtain ⟨R,hRa,hR⟩ := source_exact_remainder 10
  refine ⟨R,hRa,?_⟩
  intro a
  have ht (j : ℕ) : Tendsto (fun k => (((j+1:ℕ):ℂ) *
      (canonicalGreenJetRealStep k : ℂ))) atTop (nhds 0) := by
    have hs : Tendsto (fun k => (canonicalGreenJetRealStep k : ℂ)) atTop (nhds 0) := by
      simpa only [canonicalGreenJetRealStep_coe] using canonicalGreenJetStep_tendsto_zero
    simpa only [mul_zero] using hs.const_mul (((j+1:ℕ):ℂ))
  filter_upwards [(ht 0).eventually hR, (ht 1).eventually hR, (ht 2).eventually hR,
    (ht 3).eventually hR,
    canonicalCompletedNativeRadialProjectiveChiral_eventually_regular 4] with k h0 h1 h2 h3 hr
  rw [odd_balance_four_slopes a k (fun r => (hr r).2.1) (fun r => (hr r).2.2)]
  have hpoint (j : ℕ) : canonicalCompletedC3RadialTiltPoint k j =
      Complex.I * (((j+1:ℕ):ℂ) * (canonicalGreenJetRealStep k : ℂ)) := by
    unfold canonicalCompletedC3RadialTiltPoint canonicalCompletedC3RadialTiltStep
    rw [← canonicalGreenJetRealStep_coe]
    ring
  have heven (j : ℕ) := transverseCoefficient_even j
  have hodd (j : ℕ) := transverseCoefficient_odd j
  have he (z : ℂ) (hz : transverseSource z =
      (∑ n ∈ Finset.range 10, transverseCoefficient n*z^n)+z^10*R z) :
      (transverseSource z).re =
        (2*(h 0:ℂ)*z-2*(h 1:ℂ)*z^3+2*(h 2:ℂ)*z^5-
          2*(h 3:ℂ)*z^7+2*(h 4:ℂ)*z^9+z^10*R z).re := by
    rw [hz]
    congr 1
    norm_num [Finset.sum_range_succ, show transverseCoefficient 0 = 0 from heven 0,
      show transverseCoefficient 2 = 0 from heven 1,
      show transverseCoefficient 4 = 0 from heven 2,
      show transverseCoefficient 6 = 0 from heven 3,
      show transverseCoefficient 8 = 0 from heven 4,
      show transverseCoefficient 1 = (2*h 0:ℝ) from by convert hodd 0 using 1; norm_num [h],
      show transverseCoefficient 3 = -(2*h 1:ℝ) from by convert hodd 1 using 1; norm_num [h],
      show transverseCoefficient 5 = (2*h 2:ℝ) from by convert hodd 2 using 1; norm_num [h],
      show transverseCoefficient 7 = -(2*h 3:ℝ) from by convert hodd 3 using 1; norm_num [h],
      show transverseCoefficient 9 = (2*h 4:ℝ) from by convert hodd 4 using 1; norm_num [h]]
    ring
  have hs (j : ℕ) : radialCompletedSlope k j =
      transverseSource (((j+1:ℕ):ℂ) * (canonicalGreenJetRealStep k : ℂ)) := by
    rw [radialCompletedSlope, hpoint]; rfl
  simp only [hs]
  rw [he _ h0, he _ h1, he _ h2, he _ h3]
  simp only [← Complex.ofReal_natCast, ← Complex.ofReal_mul, ← Complex.ofReal_pow,
    Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  norm_num
  unfold oddConstant oddCorrection oddHigher oddRemainder canonicalGreenJetRealStep
  simp only [canonicalGreenJetStep, ← Complex.ofReal_natCast, ← Complex.ofReal_add,
    ← Complex.ofReal_one, ← Complex.ofReal_inv]
  generalize hK : (k:ℝ)+1 = K
  have hk : K ≠ 0 := by rw [← hK]; positivity
  field_simp
  simp only [← Complex.ofReal_ofNat, ← Complex.ofReal_mul]
  ring

end
end CarrySourceLaw
