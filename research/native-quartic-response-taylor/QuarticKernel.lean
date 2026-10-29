import CriticalFamily
import FourthBoundaryDefect

namespace CarryQuarticTaylor
open CarrySelfAdjointOperator CarryNativeTfvd CarryCommutatorControl NativeLaguerre
open CarryCriticalTfvd CarryCurvatureGreen CarryCubicTfvd CarryStencilBoundary
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

def five (a b c d e : ℂ) : ℕ →₀ ℂ :=
  Finsupp.single 0 a+Finsupp.single 1 b+Finsupp.single 2 c+
    Finsupp.single 3 d+Finsupp.single 4 e

/-- The normalized profile is only an exact factor of the OLD radial source. -/
def quarticProfile (a b t : ℝ) : ℕ →₀ ℂ :=
  fourthShape-((a*t^2 : ℝ) : ℂ) • curvatureInput-
    ((b*t^4 : ℝ) : ℂ) • Finsupp.single 0 1

theorem profile_five (a b t : ℝ) : quarticProfile a b t=
    five ((1/24 : ℂ)+(a : ℂ)*(t : ℂ)^2/2-(b : ℂ)*(t : ℂ)^4)
      (-(1/6 : ℂ)-(a : ℂ)*(t : ℂ)^2)
      ((1/4 : ℂ)+(a : ℂ)*(t : ℂ)^2/2) (-(1/6)) (1/24) := by
  ext j
  rcases j with _ | _ | _ | _ | _ | j
  all_goals simp [quarticProfile, five, fourth_shape_explicit, curvatureInput, triple] <;> ring

theorem weight_five (w : ℕ → ℂ) (a b c d e : ℂ) :
    coefficientWeight w (five a b c d e)=five (w 0*a) (w 1*b) (w 2*c) (w 3*d) (w 4*e) := by
  ext j
  rcases j with _ | _ | _ | _ | _ | j
  all_goals simp [five,coefficient_weight_apply]

theorem profile_support (a b t : ℝ) :
    (quarticProfile a b t).support ⊆ Finset.range 5 := by
  intro j hj
  by_contra hn
  have hge : 5 ≤ j := by simpa using hn
  have hz : quarticProfile a b t j=0 := by
    rw [profile_five]
    simp [five,show j≠0 by omega,show j≠1 by omega,
      show j≠2 by omega,show j≠3 by omega,show j≠4 by omega]
  exact (Finsupp.mem_support_iff.mp hj) hz

theorem commutator_five (eta : ℝ) (w : ℕ → ℂ) (a b c d e : ℂ) :
    completionCommutator eta w (five a b c d e)=
      Finsupp.single 1 ((eta : ℂ)⁻¹*(w 2-w 1)*c+(eta : ℂ)*(w 0-w 1)*a)+
      Finsupp.single 2 ((eta : ℂ)⁻¹*(w 3-w 2)*d+(eta : ℂ)*(w 1-w 2)*b)+
      Finsupp.single 3 ((eta : ℂ)⁻¹*(w 4-w 3)*e+(eta : ℂ)*(w 2-w 3)*c)+
      Finsupp.single 4 ((eta : ℂ)*(w 3-w 4)*d)+
      Finsupp.single 5 ((eta : ℂ)*(w 4-w 5)*e) := by
  ext j
  rcases j with _ | _ | _ | _ | _ | _ | j
  all_goals simp [five,completion_commutator_zero,completion_commutator_succ]

/-- Two independent complex inputs in the original Cauchy pairing. -/
theorem full_five_pairing (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (w : ℕ → ℂ) (a b c d e f g i j k : ℂ) :
    sectorKernel false eta h0 h1 w (five a b c d e) (five f g i j k)=
      conj a*(w 0*f/2+w 1*g/3+w 2*i/4+w 3*j/5+w 4*k/6)+
      conj b*(w 0*f/3+w 1*g/4+w 2*i/5+w 3*j/6+w 4*k/7)+
      conj c*(w 0*f/4+w 1*g/5+w 2*i/6+w 3*j/7+w 4*k/8)+
      conj d*(w 0*f/5+w 1*g/6+w 2*i/7+w 3*j/8+w 4*k/9)+
      conj e*(w 0*f/6+w 1*g/7+w 2*i/8+w 3*j/9+w 4*k/10) := by
  simp only [sectorKernel,sectorField,coefficientStencil,Bool.false_eq_true,ite_false]
  rw [weight_five]
  simp only [five,physicalCauchySynthesis,map_add,Finsupp.linearCombination_single,
    inner_add_left,inner_add_right,inner_smul_left,inner_smul_right,
    inner_completedNativeChiralCauchyFeature]
  norm_num
  ring

/-- Every ordered cross is retained for arbitrary weights and either sector. -/
theorem kernel_three_input_expansion (mixed : Bool) (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (w : ℕ → ℂ) (u v z : ℕ →₀ ℂ) (a b : ℝ) :
    (sectorKernel mixed eta h0 h1 w (u-(a : ℂ) • v-(b : ℂ) • z)
      (u-(a : ℂ) • v-(b : ℂ) • z)).re =
      (sectorKernel mixed eta h0 h1 w u u).re+a^2*(sectorKernel mixed eta h0 h1 w v v).re+
      b^2*(sectorKernel mixed eta h0 h1 w z z).re-
      a*(sectorKernel mixed eta h0 h1 w u v+sectorKernel mixed eta h0 h1 w v u).re-
      b*(sectorKernel mixed eta h0 h1 w u z+sectorKernel mixed eta h0 h1 w z u).re+
      a*b*(sectorKernel mixed eta h0 h1 w v z+sectorKernel mixed eta h0 h1 w z v).re := by
  simp only [sub_eq_add_neg, ← neg_smul]
  simp only [sectorKernel,map_add,map_smul,field_add_input,field_scale_input,
    inner_add_left,inner_add_right,inner_smul_left,inner_smul_right,map_neg,Complex.conj_ofReal]
  simp only [Complex.mul_re,Complex.add_re,Complex.neg_re,Complex.neg_im,
    Complex.ofReal_re,Complex.ofReal_im]
  ring

/-- Exact Cauchy identities force all four potential divergent orders to cancel.
These are spatial statements, independent of the canonical moment sequence. -/
theorem full_profile_weights (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (a b t : ℝ) :
    (sectorKernel false eta h0 h1 (monomialWeight 1) (quarticProfile a b t) (quarticProfile a b t)).re=b^2*t^8/2 ∧
    (sectorKernel false eta h0 h1 (monomialWeight 3) (quarticProfile a b t) (quarticProfile a b t)).re=
      -a*b*t^6+b^2*t^8/2 ∧
    (sectorKernel false eta h0 h1 (monomialWeight 5) (quarticProfile a b t) (quarticProfile a b t)).re=
      a^2*t^4/2-20*a*b*t^6+b^2*t^8/2-b*t^4 ∧
    (sectorKernel false eta h0 h1 (monomialWeight 7) (quarticProfile a b t) (quarticProfile a b t)).re=
      7*a^2*t^4-231*a*b*t^6+a*t^2+b^2*t^8/2-126*b*t^4 ∧
    (sectorKernel false eta h0 h1 (monomialWeight 9) (quarticProfile a b t) (quarticProfile a b t)).re=
      147*a^2*t^4/2-2290*a*b*t^6+75*a*t^2+b^2*t^8/2-6027*b*t^4+1/2 := by
  refine ⟨?_,?_,?_,?_,?_⟩
  all_goals simp only [profile_five,full_five_pairing,monomialWeight]
  all_goals norm_num [map_add,map_sub,map_div₀,map_neg,map_mul,map_pow,map_ofNat,map_one,
    Complex.conj_ofReal,Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.sub_re, ← Complex.ofReal_pow]
  all_goals ring

def quarticQuadratic (m0 m1 m2 m3 m4 a b : ℝ) : ℝ :=
  m4-2*a*m3+(a^2-2*b)*m2+2*a*b*m1+b^2*m0

def quarticPolynomialError (m1 m2 m3 m4 a b t : ℝ) : ℝ :=
  -14*a^2*m3-40*a*b*m2+150*a*m4-b^2*m1+252*b*m3+
    t^2*(147*a^2*m4+462*a*b*m3+b^2*m2-12054*b*m4)+
    t^4*(-4580*a*b*m4-b^2*m3)+b^2*m4*t^6

theorem full_weight_cancellation (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (m0 m1 m2 m3 m4 a b t : ℝ) :
    2*(m0*(sectorKernel false eta h0 h1 (monomialWeight 1) (quarticProfile a b t) (quarticProfile a b t)).re-
      m1*t^2*(sectorKernel false eta h0 h1 (monomialWeight 3) (quarticProfile a b t) (quarticProfile a b t)).re+
      m2*t^4*(sectorKernel false eta h0 h1 (monomialWeight 5) (quarticProfile a b t) (quarticProfile a b t)).re-
      m3*t^6*(sectorKernel false eta h0 h1 (monomialWeight 7) (quarticProfile a b t) (quarticProfile a b t)).re+
      m4*t^8*(sectorKernel false eta h0 h1 (monomialWeight 9) (quarticProfile a b t) (quarticProfile a b t)).re)=
      t^8*(quarticQuadratic m0 m1 m2 m3 m4 a b+t^2*quarticPolynomialError m1 m2 m3 m4 a b t) := by
  obtain ⟨hA,hB,hC,hD,hE⟩ := full_profile_weights eta h0 h1 a b t
  rw [hA,hB,hC,hD,hE]
  unfold quarticQuadratic quarticPolynomialError
  ring

theorem radial_leading_two (k : ℕ) :
    radialLeadingScalar k 2= -(((k : ℝ)+1)^2 : ℂ)/2 := by
  simpa [radialLeadingScalar] using second_scale k

theorem radial_leading_four (k : ℕ) :
    radialLeadingScalar k 4=(((k : ℝ)+1)^4 : ℂ)/24 := by
  unfold radialLeadingScalar canonicalCompletedC3RadialSecondStep canonicalGreenJetStep
  have hk : (k : ℂ)+1≠0 := by exact_mod_cast (show (k : ℝ)+1≠0 by positivity)
  field_simp [hk,Complex.I_ne_zero]
  norm_num [Complex.I_sq]
  ring

/-- Phase, 4!, seed sign and both radial powers are the existing ones. -/
theorem critical_family_profile (k : ℕ) (a b : ℝ) :
    criticalFamily k a b=((((k : ℝ)+1)^4 : ℝ) : ℂ) • quarticProfile a b (radialStep k) := by
  rw [critical_family_explicit,radial_leading_two,radial_leading_four,profile_five]
  have hk : (k : ℂ)+1≠0 := by exact_mod_cast (show (k : ℝ)+1≠0 by positivity)
  ext j
  rcases j with _ | _ | _ | _ | _ | j
  all_goals simp [five,radialStep] <;> field_simp [hk] <;> ring

theorem kernel_scale_both (mixed : Bool) (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (w : ℕ → ℂ) (r : ℝ) (c d : ℕ →₀ ℂ) :
    sectorKernel mixed eta h0 h1 w ((r : ℂ) • c) ((r : ℂ) • d)=
      (r : ℂ)^2*sectorKernel mixed eta h0 h1 w c d := by
  simp only [sectorKernel,map_smul,field_scale_input,inner_smul_left,inner_smul_right,
    Complex.conj_ofReal]
  ring

end
end CarryQuarticTaylor
