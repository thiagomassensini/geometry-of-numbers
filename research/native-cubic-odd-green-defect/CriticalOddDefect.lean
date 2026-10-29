import CriticalOddGreen

namespace CarryCubicOdd
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryCommutatorControl CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryMixedParity CarryCrossRadial CarryGreenLeading CarryGreenCubic CarryOddGreen NativeLaguerre NativeCauchyPorts
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000

/-- The four REAL coefficients of the original trial jet, before pairing. -/
def criticalBeta (a : ℝ) (k : ℕ) : Fin 4 → ℝ :=
  fun j => if (j:ℕ)=0 then -((k:ℝ)+1)^3/6-a*((k:ℝ)+1)
    else if (j:ℕ)=1 then ((k:ℝ)+1)^3/2+a*((k:ℝ)+1)
    else if (j:ℕ)=2 then -((k:ℝ)+1)^3/2 else ((k:ℝ)+1)^3/6

theorem critical_source_atoms (a : ℝ) (k : ℕ) :
    criticalOddSource a k=∑ j : Fin 4, Finsupp.single (j:ℕ) (Complex.I*(criticalBeta a k j:ℂ)) := by
  rw [critical_source_profiles,cubic_odd_profile,odd_profile_zero]
  ext j
  simp only [Fin.sum_univ_succ,Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul,
    Finsupp.single_apply,criticalBeta,Fin.val_zero,Fin.val_succ]
  rcases j with _ | _ | _ | _ | j
  all_goals norm_num
  all_goals ring

/-- The ORIGINAL Cauchy kernel on four physical atoms, not a new metric. -/
theorem kernel_four_atoms (w : ℕ → ℂ) (beta gamma : Fin 4 → ℝ) :
    kernel w (∑ i : Fin 4, Finsupp.single (i:ℕ) (Complex.I*(beta i:ℂ)))
      (∑ j : Fin 4, Finsupp.single (j:ℕ) (Complex.I*(gamma j:ℂ)))=
      ∑ i : Fin 4, ∑ j : Fin 4, (beta i:ℂ)*(gamma j:ℂ)*w j/((i:ℂ)+(j:ℂ)+2) := by
  have hw : coefficientWeight w (∑ j : Fin 4, Finsupp.single (j:ℕ) (Complex.I*(gamma j:ℂ)))=
      ∑ j : Fin 4, Finsupp.single (j:ℕ) (w j*(Complex.I*(gamma j:ℂ))) := by
    ext n
    simp only [coefficient_weight_apply,Finsupp.coe_finsetSum,Finset.sum_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hn : n=(j:ℕ)
    · simp [hn]
    · simp [Finsupp.single_eq_of_ne hn]
  change inner ℂ (physicalCauchySynthesis (∑ i : Fin 4, Finsupp.single (i:ℕ) (Complex.I*(beta i:ℂ))))
    (physicalCauchySynthesis (coefficientWeight w (∑ j : Fin 4, Finsupp.single (j:ℕ) (Complex.I*(gamma j:ℂ)))))=_
  rw [hw]
  simp only [map_sum,physicalCauchySynthesis,Finsupp.linearCombination_single,sum_inner,inner_sum,
    inner_smul_left,inner_smul_right,inner_completedNativeChiralCauchyFeature,map_mul,Complex.conj_I,Complex.conj_ofReal]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  push_cast
  ring_nf
  simp [Complex.I_sq]

/-- A readout of the synthesized kernel: only four original response samples.
This linear functional may be signed; its coefficients are not a new source. -/
def criticalSampleReadout (a b : ℝ) (k : ℕ) (w : ℕ → ℂ) : ℂ :=
  ∑ i : Fin 4, ∑ j : Fin 4, (criticalBeta a k i:ℂ)*(criticalBeta b k j:ℂ)*w j/((i:ℂ)+(j:ℂ)+2)

theorem critical_kernel_readout (a b : ℝ) (k : ℕ) (w : ℕ → ℂ) :
    kernel w (criticalOddSource a k) (criticalOddSource b k)=criticalSampleReadout a b k w := by
  rw [critical_source_atoms,critical_source_atoms,kernel_four_atoms]
  rfl

/-- Exact finite-radial defect, retaining BOTH ordered crosses and the full
analytic response, not a finite Taylor truncation. -/
theorem critical_signed_readout_exact (a b : ℝ) :
    ∀ᶠ k : ℕ in atTop,
      signedPair k (criticalOddSource a k) (criticalOddSource b k)=
        ((k:ℂ)+1)*(criticalSampleReadout a b k (responseSamples (radialStep k))+
          criticalSampleReadout b a k (responseSamples (radialStep k))) := by
  filter_upwards [odd_pairing_exact {0,1} {0,1} (trialCoeff a) (trialCoeff b)] with k hk
  have ho := odd_ordered_kernel_sum {0,1} {0,1} (trialCoeff a) (trialCoeff b) k
  simp only [oddPairing,critical_source_as_finite] at hk
  simp only [critical_source_as_finite,critical_kernel_readout] at ho
  exact hk.trans ho.symm

/-- All nine original Green crosses have the SAME exact response defect. -/
theorem critical_green_readout_exact (a b : ℝ) (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    ∀ᶠ k : ℕ in atTop,
      crossGreenPair eta h0 h1 k k (criticalOddSource a k) (criticalOddSource b k)=
        ((k:ℂ)+1)*(criticalSampleReadout a b k (responseSamples (radialStep k))+
          criticalSampleReadout b a k (responseSamples (radialStep k))) := by
  filter_upwards [critical_signed_readout_exact a b] with k hk
  rw [cross_green_eq_original]
  exact hk

/-- A pure external halo has zero COMPLETE synthesis, but two opposite fields.
This records precisely why a scalar readout cannot justify deleting a part. -/
theorem cubic_halo_fields (z : ℂ) (w : ℕ → ℂ) (hw0 : w 0=0) (hw1 : w 1=0)
    (hw2 : w 2=0) (hw3 : w 3=0) (hw4 : w 4=z)
    (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    partField eta h0 h1 w (nativeOddProfile 1) 0=
      ((Complex.I/6)*(eta:ℂ)*z) • greenColumn eta h0 h1 4 ∧
    partField eta h0 h1 w (nativeOddProfile 1) 1=0 ∧
    partField eta h0 h1 w (nativeOddProfile 1) 2=
      -(((Complex.I/6)*(eta:ℂ)*z) • greenColumn eta h0 h1 4) := by
  rw [cubic_bulk_vector,cubic_boundary_vector,cubic_residual_vector,hw0,hw1,hw2,hw3,hw4]
  simp only [zero_mul,mul_zero,sub_zero,zero_sub,add_zero,zero_add,neg_zero,zero_smul,smul_zero]
  constructor
  · module
  constructor
  · exact True.intro
  · module

/-- Explicit Cauchy coordinates of the physical trial source. -/
theorem critical_cauchy_row (a : ℝ) (k : ℕ) (j : Fin 4) :
    (∑ i : Fin 4, (criticalBeta a k i:ℂ)/((i:ℂ)+(j:ℂ)+2))=
      -((k:ℂ)+1)^3/(((j:ℂ)+2)*((j:ℂ)+3)*((j:ℂ)+4)*((j:ℂ)+5))-
      (a:ℂ)*((k:ℂ)+1)/(((j:ℂ)+2)*((j:ℂ)+3)) := by
  fin_cases j
  all_goals norm_num [criticalBeta,Fin.sum_univ_succ]
  all_goals ring

/-- Scalar coefficients read AFTER complete synthesis; no metric is changed. -/
def criticalRho (a : ℝ) (k : ℕ) (j : Fin 4) : ℝ :=
  criticalBeta a k j*
    (-((k:ℝ)+1)^3/(((j:ℝ)+2)*((j:ℝ)+3)*((j:ℝ)+4)*((j:ℝ)+5))-
      a*((k:ℝ)+1)/(((j:ℝ)+2)*((j:ℝ)+3)))

/-- On the diagonal the complete kernel is an alternating four-sample filter. -/
theorem critical_readout_four_samples (a : ℝ) (k : ℕ) (w : ℕ → ℂ) :
    criticalSampleReadout a a k w=∑ j : Fin 4, (criticalRho a k j:ℂ)*w j := by
  unfold criticalSampleReadout
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have he : (∑ i : Fin 4, (criticalBeta a k i:ℂ)*(criticalBeta a k j:ℂ)*w j/((i:ℂ)+(j:ℂ)+2))=
      (∑ i : Fin 4, (criticalBeta a k i:ℂ)/((i:ℂ)+(j:ℂ)+2))*(criticalBeta a k j:ℂ)*w j := by
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he,critical_cauchy_row]
  unfold criticalRho
  push_cast
  ring

/-- A genuine coefficient sign law, independent of canonical moment signs.
It orients the FILTER (+,-,+,-); it does not determine the filtered value. -/
theorem critical_rho_alternating (a : ℝ) (ha : 0≤a) (k : ℕ) :
    0<criticalRho a k 0 ∧ criticalRho a k 1<0 ∧
    0<criticalRho a k 2 ∧ criticalRho a k 3<0 := by
  have hk : 0<(k:ℝ)+1 := by positivity
  have hA : 0<((k:ℝ)+1)^3 := pow_pos hk 3
  have hB : 0≤a*((k:ℝ)+1) := mul_nonneg ha hk.le
  norm_num [criticalRho,criticalBeta]
  refine ⟨mul_pos_of_neg_of_neg ?_ ?_, mul_neg_of_pos_of_neg ?_ ?_,
    mul_pos_of_neg_of_neg ?_ ?_, mul_neg_of_pos_of_neg ?_ ?_⟩
  all_goals nlinarith

/-- Exact original signed defect, now with FOUR samples of the FULL response. -/
theorem critical_diagonal_four_samples_exact (a : ℝ) (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    ∀ᶠ k : ℕ in atTop,
      crossGreenPair eta h0 h1 k k (criticalOddSource a k) (criticalOddSource a k)=
        (2*((k:ℂ)+1))*(∑ j : Fin 4, (criticalRho a k j:ℂ)*responseSamples (radialStep k) j) := by
  filter_upwards [critical_green_readout_exact a a eta h0 h1] with k hk
  rw [hk,critical_readout_four_samples]
  ring

/-- A positive address weight can give a NEGATIVE ordered Cauchy readout.
This is a diagnostic weight, explicitly NOT the canonical responseSamples. -/
theorem positive_address_weight_negative :
    criticalSampleReadout 0 0 0 (fun j => if j=3 then 1 else 0)=(-1/10080:ℂ) := by
  norm_num [criticalSampleReadout,criticalBeta,Fin.sum_univ_succ]

theorem positive_address_weight_positive :
    criticalSampleReadout 0 0 0 (fun j => if (j:ℕ)=0 then 1 else 0)=(1/720:ℂ) := by
  norm_num [criticalSampleReadout,criticalBeta,Fin.sum_univ_succ]

/-- Hence positivity of address weights ALONE cannot settle the native sign.
No counterexample to the ORIGINAL completed response is claimed. -/
theorem no_sign_from_nonnegative_address_weights :
    ¬ (∀ w : ℕ → ℝ, (∀ j, 0≤w j) →
      0≤(kernel (fun j => (w j:ℂ)) (criticalOddSource 0 0) (criticalOddSource 0 0)).re) := by
  intro hh
  have hp := hh (fun j => if j=3 then 1 else 0) (by intro j; split_ifs <;> norm_num)
  rw [critical_kernel_readout] at hp
  have hv : criticalSampleReadout 0 0 0 (fun j => ((if j=3 then 1 else 0:ℝ):ℂ))=(-1/10080:ℂ) := by
    have hw : (fun j : ℕ => ((if j=3 then 1 else 0:ℝ):ℂ))=(fun j => if j=3 then (1:ℂ) else 0) := by
      funext j
      split_ifs <;> norm_num
    rw [hw]
    exact positive_address_weight_negative
  rw [hv] at hp
  norm_num at hp

end
end CarryCubicOdd
