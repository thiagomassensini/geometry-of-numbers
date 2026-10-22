import LowOrder

/-! Radial reparametrization of the INHERITED shift, tested as a comparator.
No canonical moment enters its definition. The metric is the original Cauchy metric. -/
namespace CarryRadialConservative
open CarrySelfAdjointOperator ChiralReturn NativeLaguerre CarryConservativeIntertwiner
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000

def radialSymbol (k j : ℕ) : ℝ := (2*(j:ℝ)+1-k)/(2*j+k+3)
def radialPortCoefficient (k j : ℕ) : ℝ := 2*((k:ℝ)+1)/(2*j+k+3)

theorem radial_den_pos (k j : ℕ) : 0<(2*(j:ℝ)+k+3) := by positivity

theorem radial_symbol_shift (k j : ℕ) :
    radialSymbol k j=(rho j-(k:ℝ)/(k+2))/(1-(k:ℝ)/(k+2)*rho j) := by
  have hk : (k:ℝ)+2≠0 := by positivity
  have hj : 2*(j:ℝ)+3≠0 := by positivity
  have hd : 1-(k:ℝ)/(k+2)*rho j≠0 := by
    have hka : (k:ℝ)/(k+2)<1 := (div_lt_one (by positivity)).mpr (by linarith)
    have hm : (k:ℝ)/(k+2)*rho j<1 := by
      calc
        _ < 1*rho j := mul_lt_mul_of_pos_right hka (rho_pos j)
        _ = rho j := one_mul _
        _ < 1 := rho_lt_one j
    exact ne_of_gt (sub_pos.mpr hm)
  apply (eq_div_iff hd).mpr
  unfold radialSymbol rho
  field_simp [hk,hj,ne_of_gt (radial_den_pos k j)]
  ring

theorem radial_symbol_scaled_address (k j : ℕ) :
    radialSymbol k j=
      (2*(((j:ℝ)+1)/((k:ℝ)+1))-1)/(2*(((j:ℝ)+1)/((k:ℝ)+1))+1) := by
  have hk : (k:ℝ)+1≠0 := by positivity
  have hd : 2*(((j:ℝ)+1)/((k:ℝ)+1))+1≠0 := by positivity
  unfold radialSymbol
  field_simp
  ring

/-- Rank-one conservation in the ORIGINAL radial Cauchy Gram. -/
theorem scalar_conservation (k i j : ℕ) :
    ((k:ℝ)+1)/((i:ℝ)+j+2)*(1-radialSymbol k i*radialSymbol k j)=
      radialPortCoefficient k i*radialPortCoefficient k j := by
  have hi := ne_of_gt (radial_den_pos k i)
  have hj := ne_of_gt (radial_den_pos k j)
  have hij : (i:ℝ)+j+2≠0 := by positivity
  unfold radialSymbol radialPortCoefficient
  field_simp
  ring

def conservativeSynthesis (k N : ℕ) (c : Fin N → ℂ) : CanonicalCompletedNativeChiralCauchyCarrier :=
  ∑ i, c i • ((radialSymbol k i:ℂ) • completedNativeRadialChiralCauchyState k i)

def conservativePort (k N : ℕ) (c : Fin N → ℂ) : ℂ :=
  ∑ i, c i*(radialPortCoefficient k i:ℂ)

/-- Two independent coefficient vectors are synthesized before observation. -/
theorem polarized_conservation (k N : ℕ) (c d : Fin N → ℂ) :
    inner ℂ (radialIncidentSynthesis k N c) (radialIncidentSynthesis k N d)-
      inner ℂ (conservativeSynthesis k N c) (conservativeSynthesis k N d)=
      conj (conservativePort k N c)*conservativePort k N d := by
  classical
  simp only [radialIncidentSynthesis,conservativeSynthesis,conservativePort,
    LinearMap.coe_mk,AddHom.coe_mk,sum_inner,inner_sum,inner_smul_left,inner_smul_right,
    inner_completedNativeRadialChiralCauchyState,map_sum,map_mul,Complex.conj_ofReal,
    Finset.sum_mul,Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have h := congrArg Complex.ofReal (scalar_conservation k i j)
  push_cast at h
  push_cast
  linear_combination conj (c j)*d i*h

theorem conservative_energy (k N : ℕ) (c : Fin N → ℂ) :
    ‖radialIncidentSynthesis k N c‖^2-‖conservativeSynthesis k N c‖^2=
      ‖conservativePort k N c‖^2 := by
  have h := congrArg Complex.re (polarized_conservation k N c c)
  simp only [Complex.sub_re] at h
  have hs (z : CanonicalCompletedNativeChiralCauchyCarrier) : (inner ℂ z z).re=‖z‖^2 :=
    (norm_sq_eq_re_inner (𝕜:=ℂ) z).symm
  rw [hs,hs] at h
  have hp : (conj (conservativePort k N c)*conservativePort k N c).re=
      ‖conservativePort k N c‖^2 := by
    rw [Complex.conj_mul']
    norm_cast
  exact h.trans hp

/-- Finite boundedness uses the inherited incident coordinates, not whitening. -/
def conservativeTransfer (k N : ℕ) :
    RadialIncidentSpan k N →L[ℂ] CanonicalCompletedNativeChiralCauchyCarrier :=
  letI := (radialIncidentSynthesis k N).finiteDimensional_range
  let D : (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ) :=
    { toFun := fun c i => c i*(radialSymbol k i:ℂ)
      map_add' := by intros; ext; simp [add_mul]
      map_smul' := by intros; ext; simp [mul_assoc] }
  (((radialIncidentSynthesis k N).comp D).comp
    (radialIncidentCoordinates k N).toLinearMap).toContinuousLinearMap

theorem conservativeTransfer_exact (k N : ℕ) (c : Fin N → ℂ) :
    conservativeTransfer k N (radialIncidentVector k N c)=conservativeSynthesis k N c := by
  change radialIncidentSynthesis k N ((fun (c : Fin N → ℂ) (i : Fin N) => c i*(radialSymbol k i:ℂ))
      ((radialIncidentCoordinates k N) ((radialIncidentCoordinates k N).symm c)))=_
  rw [LinearEquiv.apply_symm_apply]
  simp only [radialIncidentSynthesis,conservativeSynthesis,LinearMap.coe_mk,AddHom.coe_mk,smul_smul]

theorem conservativeTransfer_contractive (k N : ℕ) : ‖conservativeTransfer k N‖≤1 := by
  apply (ContinuousLinearMap.opNorm_le_iff (by norm_num : (0:ℝ)≤1)).mpr
  intro x
  obtain ⟨c,rfl⟩ := (radialIncidentCoordinates k N).symm.surjective x
  change ‖conservativeTransfer k N (radialIncidentVector k N c)‖≤1*‖radialIncidentVector k N c‖
  rw [conservativeTransfer_exact,radialIncidentVector_norm,one_mul]
  have h := conservative_energy k N c
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by nlinarith [sq_nonneg ‖conservativePort k N c‖])

/-- Exact prefix coherence at fixed radial parameter, before any kernel readout. -/
theorem conservativeSynthesis_snoc_zero (k N : ℕ) (c : Fin N → ℂ) :
    conservativeSynthesis k (N+1) (Fin.snoc c 0)=conservativeSynthesis k N c := by
  simp [conservativeSynthesis,Fin.sum_univ_castSucc]

theorem conservativePort_snoc_zero (k N : ℕ) (c : Fin N → ℂ) :
    conservativePort k (N+1) (Fin.snoc c 0)=conservativePort k N c := by
  simp [conservativePort,Fin.sum_univ_castSucc]

end
end CarryRadialConservative
