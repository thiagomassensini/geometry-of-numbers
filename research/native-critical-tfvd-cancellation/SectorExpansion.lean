import PhysicalKernels

namespace CarryCriticalTfvd
open CarrySelfAdjointOperator CarryNativeTfvd CarryCommutatorControl NativeLaguerre
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 180000

def sectorFlux (mixed : Bool) (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (k : ℕ) (c : ℕ →₀ ℂ) : ℝ :=
  2*((k : ℝ)+1)*(sectorKernel mixed eta h0 h1 (responseWeight k) c c).im

theorem full_original_flux (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (k : ℕ) (a : ℝ)
    (hF : ∀ j : Fin 4, completedNativeOperatorCharacteristic
      (canonicalCompletedC3RadialTiltPoint k j) ≠ 0)
    (hd : ∀ j : ℕ, j < 4 → incidentWeight k j-returnedWeight k j=chiralDifference) :
    fullEnergy k (criticalInput k a)=sectorFlux false eta h0 h1 k (criticalInput k a) := by
  exact full_response_flux k _ (critical_input_support k a)
    (fun j => hF ⟨j,by omega⟩) (fun j hj => hd j (by omega))

theorem mixed_original_flux (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (k : ℕ) (a : ℝ)
    (hF : ∀ j : Fin 4, completedNativeOperatorCharacteristic
      (canonicalCompletedC3RadialTiltPoint k j) ≠ 0)
    (hd : ∀ j : ℕ, j < 4 → incidentWeight k j-returnedWeight k j=chiralDifference) :
    mixedEnergy eta h0 h1 k (criticalInput k a)=sectorFlux true eta h0 h1 k (criticalInput k a) :=
  mixed_response_flux eta h0 h1 k _ (critical_input_support k a) hF hd

def poleFour (mixed : Bool) (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) : ℝ :=
  2*h 0*spatialU mixed eta h0 h1 (monomialWeight 1)
def poleTwo (mixed : Bool) (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (a : ℝ) : ℝ :=
  2*a*h 0*spatialV mixed eta h0 h1 (monomialWeight 1) -
  2*h 1*spatialU mixed eta h0 h1 (monomialWeight 3)
def finitePart (mixed : Bool) (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (a : ℝ) : ℝ :=
  2*a^2*h 0*spatialW mixed eta h0 h1 (monomialWeight 1) -
  2*a*h 1*spatialV mixed eta h0 h1 (monomialWeight 3) +
  2*h 2*spatialU mixed eta h0 h1 (monomialWeight 5)

/-- The analytic remainder is retained with all three stencil outputs and
the outgoing weight at address 3. Monomial tests only extract Taylor terms. -/
def sectorError (mixed : Bool) (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (R : ℂ → ℂ) (a t : ℝ) : ℝ :=
  -2*a^2*h 1*spatialW mixed eta h0 h1 (monomialWeight 3) +
  2*a*h 2*spatialV mixed eta h0 h1 (monomialWeight 5) +
  2*a^2*h 2*t^2*spatialW mixed eta h0 h1 (monomialWeight 5) +
  2*spatialU mixed eta h0 h1 (remainderWeight R t) +
  2*a*t^2*spatialV mixed eta h0 h1 (remainderWeight R t) +
  2*a^2*t^4*spatialW mixed eta h0 h1 (remainderWeight R t)

theorem kernel_congr (mixed : Bool) (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (w z : ℕ → ℂ) (c d : ℕ →₀ ℂ) (hd : d.support ⊆ Finset.range 3)
    (he : ∀ j : Fin 4, w j=z j) :
    sectorKernel mixed eta h0 h1 w c d=sectorKernel mixed eta h0 h1 z c d := by
  unfold sectorKernel sectorField
  rw [stencil_congr mixed eta w z d hd he]

theorem sector_flux_exact_expansion :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧ ∀ (mixed : Bool) (eta : ℝ)
      (h0 : 0 < eta) (h1 : eta < 1) (a : ℝ), ∀ᶠ k : ℕ in atTop,
      sectorFlux mixed eta h0 h1 k (criticalInput k a) =
        ((k : ℝ)+1)^4*poleFour mixed eta h0 h1 +
        ((k : ℝ)+1)^2*poleTwo mixed eta h0 h1 a + finitePart mixed eta h0 h1 a +
        radialStep k^2*sectorError mixed eta h0 h1 R a (radialStep k) := by
  obtain ⟨R,hR,he⟩ := response_weight_taylor
  refine ⟨R,hR,?_⟩
  intro mixed eta h0 h1 a
  filter_upwards [he] with k hk
  let w : ℕ → ℂ := fun j => Complex.I*
    (((h 0 : ℂ)*(radialStep k : ℂ))*monomialWeight 1 j+
      (-(h 1 : ℂ)*(radialStep k : ℂ)^3)*monomialWeight 3 j+
      ((h 2 : ℂ)*(radialStep k : ℂ)^5)*monomialWeight 5 j+
      ((radialStep k : ℂ)^7)*remainderWeight R (radialStep k) j)
  have hw (j : Fin 4) : responseWeight k j=w j := by
    rw [hk j]; dsimp [w]; ring
  unfold sectorFlux
  rw [kernel_congr mixed eta h0 h1 (responseWeight k) w _ _ (critical_input_support k a) hw]
  dsimp only [w]
  rw [kernel_scale_weight mixed eta h0 h1 Complex.I]
  rw [kernel_four_weights mixed eta h0 h1]
  simp only [Complex.mul_im,Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_add,
    Complex.mul_re,Complex.add_re,Complex.ofReal_re,Complex.ofReal_im,
    ← Complex.ofReal_pow,← Complex.ofReal_mul,← Complex.ofReal_neg,sub_zero]
  simp only [kernel_critical_real]
  unfold poleFour poleTwo finitePart sectorError
  generalize spatialU mixed eta h0 h1 (monomialWeight 1)=U1
  generalize spatialV mixed eta h0 h1 (monomialWeight 1)=V1
  generalize spatialW mixed eta h0 h1 (monomialWeight 1)=W1
  generalize spatialU mixed eta h0 h1 (monomialWeight 3)=U3
  generalize spatialV mixed eta h0 h1 (monomialWeight 3)=V3
  generalize spatialW mixed eta h0 h1 (monomialWeight 3)=W3
  generalize spatialU mixed eta h0 h1 (monomialWeight 5)=U5
  generalize spatialV mixed eta h0 h1 (monomialWeight 5)=V5
  generalize spatialW mixed eta h0 h1 (monomialWeight 5)=W5
  generalize spatialU mixed eta h0 h1 (remainderWeight R (radialStep k))=UR
  generalize spatialV mixed eta h0 h1 (remainderWeight R (radialStep k))=VR
  generalize spatialW mixed eta h0 h1 (remainderWeight R (radialStep k))=WR
  unfold radialStep
  generalize hk : (k : ℝ)+1=K
  have hK : K≠0 := by rw [← hk]; positivity
  field_simp [hK]
  ring

theorem sector_error_continuous (mixed : Bool) (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (R : ℂ → ℂ) (hR : AnalyticAt ℂ R 0) (a : ℝ) :
    ContinuousAt (sectorError mixed eta h0 h1 R a) 0 := by
  have hdd := remainder_kernel_continuous mixed eta h0 h1 R hR curvatureInput (-(1/2)) 1 (-(1/2))
  have hde := remainder_kernel_continuous mixed eta h0 h1 R hR curvatureInput (-1) 0 0
  have hed := remainder_kernel_continuous mixed eta h0 h1 R hR seedInput (-(1/2)) 1 (-(1/2))
  have hee := remainder_kernel_continuous mixed eta h0 h1 R hR seedInput (-1) 0 0
  have hU : ContinuousAt (fun t : ℝ => spatialU mixed eta h0 h1 (remainderWeight R t)) 0 := hdd
  have hV : ContinuousAt (fun t : ℝ => spatialV mixed eta h0 h1 (remainderWeight R t)) 0 := by
    have hv := hde.add hed
    change ContinuousAt (fun t : ℝ =>
      (sectorKernel mixed eta h0 h1 (remainderWeight R t) curvatureInput (triple (-1) 0 0)).re +
      (sectorKernel mixed eta h0 h1 (remainderWeight R t) seedInput (triple (-(1/2)) 1 (-(1/2)))).re) 0 at hv
    simpa only [spatialV,Complex.add_re,curvatureInput,seedInput] using hv
  have hW : ContinuousAt (fun t : ℝ => spatialW mixed eta h0 h1 (remainderWeight R t)) 0 := hee
  unfold sectorError
  fun_prop

theorem sector_finite_part_limit (mixed : Bool) (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (a : ℝ) :
    Tendsto (fun k : ℕ => sectorFlux mixed eta h0 h1 k (criticalInput k a) -
      ((k : ℝ)+1)^4*poleFour mixed eta h0 h1 - ((k : ℝ)+1)^2*poleTwo mixed eta h0 h1 a)
      atTop (nhds (finitePart mixed eta h0 h1 a)) := by
  obtain ⟨R,hR,he⟩ := sector_flux_exact_expansion
  have hr := (sector_error_continuous mixed eta h0 h1 R hR a).tendsto.comp radial_step_tendsto
  have ht := (tendsto_const_nhds (x := finitePart mixed eta h0 h1 a)).add
    ((radial_step_tendsto.pow 2).mul hr)
  simp only [zero_pow (by decide : 2≠0),zero_mul,add_zero] at ht
  apply ht.congr'
  filter_upwards [he mixed eta h0 h1 a] with k hk
  rw [hk]; dsimp only [Function.comp_def]; ring

theorem sector_second_order_error_bound (mixed : Bool) (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (a : ℝ) :
    ∃ M : ℝ, 0<M ∧ ∀ᶠ k : ℕ in atTop,
      |sectorFlux mixed eta h0 h1 k (criticalInput k a) -
        ((k : ℝ)+1)^4*poleFour mixed eta h0 h1 - ((k : ℝ)+1)^2*poleTwo mixed eta h0 h1 a -
        finitePart mixed eta h0 h1 a| ≤ M*radialStep k^2 := by
  obtain ⟨R,hR,he⟩ := sector_flux_exact_expansion
  let M := |sectorError mixed eta h0 h1 R a 0|+1
  refine ⟨M,by dsimp [M]; positivity,?_⟩
  have ht := (sector_error_continuous mixed eta h0 h1 R hR a).tendsto.comp radial_step_tendsto
  have hb := ht.abs.eventually (gt_mem_nhds (show |sectorError mixed eta h0 h1 R a 0|<M by dsimp [M]; linarith))
  filter_upwards [he mixed eta h0 h1 a,hb] with k hk hbound
  rw [hk]
  have hz : ((k : ℝ)+1)^4*poleFour mixed eta h0 h1 + ((k : ℝ)+1)^2*poleTwo mixed eta h0 h1 a +
      finitePart mixed eta h0 h1 a + radialStep k^2*sectorError mixed eta h0 h1 R a (radialStep k) -
      ((k : ℝ)+1)^4*poleFour mixed eta h0 h1 - ((k : ℝ)+1)^2*poleTwo mixed eta h0 h1 a -
      finitePart mixed eta h0 h1 a = radialStep k^2*sectorError mixed eta h0 h1 R a (radialStep k) := by ring
  rw [hz,abs_mul,abs_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ radialStep k^2*M := mul_le_mul_of_nonneg_left hbound.le (sq_nonneg _)
    _ = _ := mul_comm _ _

end
end CarryCriticalTfvd
