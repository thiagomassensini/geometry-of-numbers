import FinitePorts
import OddAsymptotics
import CarrySelfAdjointOperator.NativeSourceAllOrderSchur

namespace CarryInteriorGreen
open CarryFirstOddGreen CarryFiniteGreen CarryRadialGreen CarryMeanContrast CarryRadialRefinement CarryPhysicalTrace CarrySelfAdjointOperator
open CarrySelfAdjointOperator.NativeLaguerre Filter Topology
open scoped ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem three_regular_eventually : ∀ᶠ k : ℕ in atTop, threeRegular k := by
  filter_upwards [canonicalCompletedNativeRadialProjectiveChiral_eventually_regular 4] with k hk
  exact fun i => (hk i).2

theorem finite_prefix_eventually (x : ℕ →₀ ℂ) :
    ∀ᶠ k : ℕ in atTop, ∀ j∈x.support, prefixRegular k j := by
  obtain ⟨N,hN⟩ := Finset.exists_nat_subset_range x.support
  filter_upwards [canonicalCompletedNativeRadialProjectiveChiral_eventually_regular (N+1)] with k hk
  intro j hj i hi
  have hjN : j<N := Finset.mem_range.mp (hN hj)
  exact (hk ⟨i,by omega⟩).2

theorem finite_residual_eventually_closed (η : ℝ) (hη : η≠0) (x : ℕ →₀ ℂ) :
    ∀ᶠ k : ℕ in atTop, reconstructedResidual 0 η k x=
      (finiteResidualFeature η k x,finiteResidualFeature η k x) := by
  filter_upwards [finite_prefix_eventually x] with k hk
  exact finite_residual_closed η hη k x hk

def criticalPairing (k l : ℕ) (a b : ℝ) : ℂ :=
  physicalForm (pairPower l (completedSource k (criticalInput k a)))
    (pairPower k (completedSource l (criticalInput l b)))

theorem form_smul_left (a : ℂ) (x y : PhysicalPair) :
    physicalForm (a • x) y=conj a*physicalForm x y := by
  simpa only [one_smul,mul_one] using physical_form_smul a 1 x y

theorem form_smul_right (a : ℂ) (x y : PhysicalPair) :
    physicalForm x (a • y)=a*physicalForm x y := by
  simpa only [one_smul,map_one,one_mul] using physical_form_smul 1 a x y

/-- Independent radial indices and independent coefficients. This preserves
polarization, not merely the diagonal of the critical energy. -/
theorem critical_pairing_four (k l : ℕ) (a b : ℝ) :
    criticalPairing k l a b=commonJetPairing k l 2 2-
      (b : ℂ)*commonJetPairing k l 2 0-
      (a : ℂ)*commonJetPairing k l 0 2+
      (a : ℂ)*(b : ℂ)*commonJetPairing k l 0 0 := by
  simp only [criticalPairing,critical_source_original,map_sub,map_smul]
  rw [form_sub_sub,form_smul_right,form_smul_left,physical_form_smul]
  simp only [Complex.conj_ofReal,commonJetPairing]

theorem critical_pairing_limit (a b : ℝ) :
    Tendsto (fun steps : ℕ × ℕ => criticalPairing steps.1 steps.2 a b) atTop
      (nhds ((canonicalCompletedNativeLogDerivativeMoment 2-
        (a+b)*canonicalCompletedNativeLogDerivativeMoment 1+
        a*b*canonicalCompletedNativeLogDerivativeMoment 0 : ℝ) : ℂ)) := by
  have h := (((common_even_jets 1 1).sub ((common_even_jets 1 0).const_mul (b : ℂ))).sub
    ((common_even_jets 0 1).const_mul (a : ℂ))).add
    ((common_even_jets 0 0).const_mul ((a : ℂ)*(b : ℂ)))
  have ht : (canonicalCompletedNativeLogDerivativeMoment 2 : ℂ)-
      (b : ℂ)*(canonicalCompletedNativeLogDerivativeMoment 1 : ℂ)-
      (a : ℂ)*(canonicalCompletedNativeLogDerivativeMoment 1 : ℂ)+
      (a : ℂ)*(b : ℂ)*(canonicalCompletedNativeLogDerivativeMoment 0 : ℂ)=
      ((canonicalCompletedNativeLogDerivativeMoment 2-(a+b)*canonicalCompletedNativeLogDerivativeMoment 1+
        a*b*canonicalCompletedNativeLogDerivativeMoment 0 : ℝ) : ℂ) := by push_cast; ring
  change Tendsto (fun steps : ℕ × ℕ =>
    commonJetPairing steps.1 steps.2 2 2-(b : ℂ)*commonJetPairing steps.1 steps.2 2 0-
      (a : ℂ)*commonJetPairing steps.1 steps.2 0 2+
      (a : ℂ)*(b : ℂ)*commonJetPairing steps.1 steps.2 0 0) atTop (nhds _) at h
  rw [ht] at h
  simpa only [critical_pairing_four] using h

theorem critical_source_limit (a : ℝ) :
    Tendsto (fun (k : ℕ) => (physicalForm (completedSource k (criticalInput k a))
      (completedSource k (criticalInput k a))).re) atTop
      (nhds (canonicalCompletedNativeLogDerivativeMoment 2-2*a*canonicalCompletedNativeLogDerivativeMoment 1+
        a^2*canonicalCompletedNativeLogDerivativeMoment 0)) := by
  have hd : Tendsto (fun k : ℕ => (k,k)) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_id.prodMk tendsto_id
  have h := Complex.continuous_re.continuousAt.tendsto.comp ((critical_pairing_limit a a).comp hd)
  simp only [Function.comp_def,criticalPairing,form_same_power,Complex.ofReal_re] at h
  convert h using 1
  ring

theorem critical_green_limit (η : ℝ) (hη0 : 0<η) (hη1 : η<1) (a : ℝ) :
    Tendsto (fun (k : ℕ) => (physicalForm (criticalBulk η k a) (criticalBulk η k a)).re+
      2*(physicalForm (criticalBulk η k a) (criticalResidual η k a)).re) atTop
      (nhds (canonicalCompletedNativeLogDerivativeMoment 2-2*a*canonicalCompletedNativeLogDerivativeMoment 1+
        a^2*canonicalCompletedNativeLogDerivativeMoment 0)) := by
  apply (critical_source_limit a).congr'
  filter_upwards [three_regular_eventually] with k hr
  rw [critical_source_original]
  exact critical_energy_three_sectors η hη0 hη1 k hr a

theorem first_source_schur_eq (m : ℕ → ℝ) :
    sourceMomentSchur m 0 1=m 2-m 1^2/m 0 := by
  simp [sourceMomentSchur,sourceMomentCoupling,sourceMomentMatrix,
    Matrix.inv_subsingleton,Matrix.mulVec,dotProduct,Ring.inverse_eq_inv]
  ring

/-- The SAME named sourceMomentSchur used by PR41, receiving ONLY h0 != 0.
Its sign is not assumed, and the old boundary-energy factor 4 is not changed. -/
theorem schur_green_limit (η : ℝ) (hη0 : 0<η) (hη1 : η<1)
    (hh0 : canonicalCompletedNativeLogDerivativeMoment 0≠0) :
    Tendsto (fun (k : ℕ) =>
      (physicalForm (criticalBulk η k (canonicalCompletedNativeLogDerivativeMoment 1/
          canonicalCompletedNativeLogDerivativeMoment 0))
        (criticalBulk η k (canonicalCompletedNativeLogDerivativeMoment 1/
          canonicalCompletedNativeLogDerivativeMoment 0))).re+
      2*(physicalForm (criticalBulk η k (canonicalCompletedNativeLogDerivativeMoment 1/
          canonicalCompletedNativeLogDerivativeMoment 0))
        (criticalResidual η k (canonicalCompletedNativeLogDerivativeMoment 1/
          canonicalCompletedNativeLogDerivativeMoment 0))).re) atTop
      (nhds (sourceMomentSchur canonicalCompletedNativeLogDerivativeMoment 0 1)) := by
  rw [first_source_schur_eq]
  convert critical_green_limit η hη0 hη1
    (canonicalCompletedNativeLogDerivativeMoment 1/canonicalCompletedNativeLogDerivativeMoment 0) using 1
  field_simp [hh0]
  ring

/-- Positivity is equivalent to the original remaining scalar Schur gap;
the exact Green reconstruction did not remove that obligation. -/
theorem critical_limit_complete_square (a : ℝ)
    (hh0 : canonicalCompletedNativeLogDerivativeMoment 0≠0) :
    canonicalCompletedNativeLogDerivativeMoment 2-2*a*canonicalCompletedNativeLogDerivativeMoment 1+
      a^2*canonicalCompletedNativeLogDerivativeMoment 0=
      canonicalCompletedNativeLogDerivativeMoment 2-
        canonicalCompletedNativeLogDerivativeMoment 1^2/canonicalCompletedNativeLogDerivativeMoment 0+
      canonicalCompletedNativeLogDerivativeMoment 0*
        (a-canonicalCompletedNativeLogDerivativeMoment 1/canonicalCompletedNativeLogDerivativeMoment 0)^2 := by
  field_simp [hh0]
  ring

end
end CarryInteriorGreen
