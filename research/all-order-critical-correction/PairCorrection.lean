import RadialPairing

namespace CarryAllOrderCorrection
open CarrySelfAdjointOperator CarrySourceLaw Filter Topology
open scoped BigOperators ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

/-- Cancellation order forced by the ORIGINAL finite-difference stencils. -/
theorem raw_parity_below (i j s : ℕ) {d : ℕ} (hd : d < 2*i+s+(2*j+s)+1) :
    taylorCoefficient (rawGreenRay (2*i+s) (2*j+s)) d = 0 := by
  rcases Nat.even_or_odd d with ⟨a,ha⟩ | ⟨a,ha⟩
  · rw [show d=2*a by omega,rawGreenRay_even]
  · rw [show d=2*a+1 by omega,rawGreenRay_odd,
      greenContraction_below (by omega : 2*a<2*i+s+(2*j+s))]
    simp

theorem combined_parity_sign (i j s : ℕ) :
    (-1:ℂ)^(i+j+s)*(-1:ℂ)^(2*i+s) = (-1:ℂ)^(i+j) := by
  rw [← pow_add,show i+j+s+(2*i+s)=(i+j)+2*(i+s) by omega,pow_add,pow_mul]
  norm_num

theorem raw_parity_leading (i j s : ℕ) :
    taylorCoefficient (rawGreenRay (2*i+s) (2*j+s)) (2*i+s+(2*j+s)+1) =
      (-1:ℂ)^(i+j)*((2*i+s).factorial:ℂ)*((2*j+s).factorial:ℂ)*
        (canonicalCompletedNativeLogDerivativeMoment (i+j+s):ℂ) := by
  rw [show 2*i+s+(2*j+s)+1=2*(i+j+s)+1 by omega,rawGreenRay_odd,
    show 2*(i+j+s)=2*i+s+(2*j+s) by omega,greenContraction_leading]
  push_cast
  calc
    _ = ((-1:ℂ)^(i+j+s)*(-1:ℂ)^(2*i+s))*
        ((2*i+s).factorial:ℂ)*((2*j+s).factorial:ℂ)*
          (canonicalCompletedNativeLogDerivativeMoment (i+j+s):ℂ) := by ring
    _ = _ := by rw [combined_parity_sign]

theorem raw_parity_next_zero (i j s : ℕ) :
    taylorCoefficient (rawGreenRay (2*i+s) (2*j+s)) (2*i+s+(2*j+s)+1+1) = 0 := by
  rw [show 2*i+s+(2*j+s)+1+1=2*(i+j+s+1) by omega,rawGreenRay_even]

theorem raw_parity_second (i j s : ℕ) :
    taylorCoefficient (rawGreenRay (2*i+s) (2*j+s)) (2*i+s+(2*j+s)+1+2) =
      (-1:ℂ)^(i+j)*((2*i+s).factorial:ℂ)*((2*j+s).factorial:ℂ)*
        ((canonicalCompletedNativeLogDerivativeMoment (i+j+s+1)*
          correctionWeight (2*i+s) (2*j+s):ℝ):ℂ) := by
  rw [show 2*i+s+(2*j+s)+1+2=2*(i+j+s+1)+1 by omega,rawGreenRay_odd,
    show 2*(i+j+s+1)=2*i+s+(2*j+s)+2 by omega,greenContraction_second]
  push_cast
  rw [pow_succ]
  unfold correctionWeight
  calc
    _ = ((-1:ℂ)^(i+j+s)*(-1:ℂ)^(2*i+s))*
        ((2*i+s).factorial:ℂ)*((2*j+s).factorial:ℂ)*
        (canonicalCompletedNativeLogDerivativeMoment (i+j+s+1):ℂ)*
        ((firstStencilSurplus (2*i+s):ℂ)*(firstStencilSurplus (2*j+s):ℂ)-
          (secondStencilSurplus (2*i+s):ℂ)-(secondStencilSurplus (2*j+s):ℂ)) := by ring
    _ = _ := by rw [combined_parity_sign]; push_cast; ring

theorem phaseFactor_cancels (i j s : ℕ) (z : ℂ) :
    phaseFactor i j s*((-1:ℂ)^(i+j)*((2*i+s).factorial:ℂ)*((2*j+s).factorial:ℂ)*z)=z := by
  have hf : ((2*i+s).factorial:ℂ) ≠ 0 := by exact_mod_cast (2*i+s).factorial_ne_zero
  have hg : ((2*j+s).factorial:ℂ) ≠ 0 := by exact_mod_cast (2*j+s).factorial_ne_zero
  have hs : ((-1:ℂ)^(i+j))^2 = 1 := by
    rw [← pow_mul,Nat.mul_comm (i+j) 2,pow_mul]
    norm_num
  calc
    _ = ((-1:ℂ)^(i+j))^2*z := by unfold phaseFactor; field_simp
    _ = z := by rw [hs]; ring

/-- ALL pairs in every canonical parity sector: the full physical signed
pairing has its explicit second correction, with no pivot or positivity
premise and no discarded analytic remainder. -/
theorem projective_pairing_second_correction (i j s : ℕ) :
    Tendsto (fun k : ℕ => ((k:ℂ)+1)^2 *
      (canonicalCompletedNativeProjectiveChiralForm
        (projectiveChiralDifferenceJet k (2*i+s)) (projectiveChiralDifferenceJet k (2*j+s)) -
        (canonicalCompletedNativeLogDerivativeMoment (i+j+s):ℂ))) atTop
      (nhds ((canonicalCompletedNativeLogDerivativeMoment (i+j+s+1)*
        correctionWeight (2*i+s) (2*j+s):ℝ):ℂ)) := by
  have ht := (analytic_second_coefficient_tendsto
    (rawGreenRay_analytic (2*i+s) (2*j+s)) (2*i+s+(2*j+s)+1)
    (fun d hd => raw_parity_below i j s hd) (raw_parity_next_zero i j s)).const_mul
      (phaseFactor i j s)
  rw [raw_parity_second,phaseFactor_cancels] at ht
  have hc : phaseFactor i j s *
      taylorCoefficient (rawGreenRay (2*i+s) (2*j+s)) (2*i+s+(2*j+s)+1) =
      (canonicalCompletedNativeLogDerivativeMoment (i+j+s):ℂ) := by
    rw [raw_parity_leading,phaseFactor_cancels]
  apply ht.congr'
  filter_upwards [projective_pairing_eventually_ray i j s] with k hk
  rw [hk,← hc]
  ring

end
end CarryAllOrderCorrection
