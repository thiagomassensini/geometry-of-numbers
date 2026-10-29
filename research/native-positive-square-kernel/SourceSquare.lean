import PolarizedEuler
import CarrySelfAdjointOperator.CompletedNativeChiralReturnEnergyPort

namespace CarryPositiveSquare
open CarrySelfAdjointOperator ChiralReturn CarryJetOverlap CarryFiberTransport CarryResidualEuler
open scoped InnerProductSpace ComplexConjugate BigOperators
open Filter Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- Literal source-generated Jordan ports in the unchanged physical carrier. -/
def positiveSourceJet (n k : ℕ) (x : Fin (2*n) → ℂ) :=
  radialReturnJordanPositivePort k (2*n)
    (radialIncidentVector k (2*n) (nativeSourceChiralJetInput n k x))
def negativeSourceJet (n k : ℕ) (x : Fin (2*n) → ℂ) :=
  radialReturnJordanNegativePort k (2*n)
    (radialIncidentVector k (2*n) (nativeSourceChiralJetInput n k x))

/-- Exact comparison of the two positive factors with the whole original
kernel, in TWO independent arguments. The negative Gram remains explicit. -/
theorem source_jordan_budget (n k : ℕ) (x y : Fin (2*n) → ℂ)
    (hs : strip k (2*n))
    (hp : ∀ i : Fin (2*n), completedNativePositiveHermiteBiehlerCoordinate (radialPoint k i) ≠ 0) :
    inner ℂ (positiveSourceJet n k x) (positiveSourceJet n k y)-
      inner ℂ (negativeSourceJet n k x) (negativeSourceJet n k y) =
        2*jetBudget n k x y hs := by
  rw [jetBudget_eq_original_pairing n k x y hs hp,
    jet_pairing_source_balance n k x y hp]
  have hj := radialReturnJordanPorts_pairing k (2*n)
    (radialIncidentVector k (2*n) (nativeSourceChiralJetInput n k x))
    (radialIncidentVector k (2*n) (nativeSourceChiralJetInput n k y))
  change _ = inner ℂ
    (radialIncidentVector k (2*n) (nativeSourceChiralJetInput n k x) : CanonicalCompletedNativeChiralCauchyCarrier)
    (radialIncidentVector k (2*n) (nativeSourceChiralJetInput n k y) : CanonicalCompletedNativeChiralCauchyCarrier)-_ at hj
  rw [radialReturnTransfer_polarized_balance k (2*n) _ _ hp] at hj
  simpa [positiveSourceJet,negativeSourceJet] using hj

theorem source_jordan_euler (n k : ℕ) (x y : Fin (2*(n+1)) → ℂ)
    (hs : strip k (2*(n+1)))
    (hf : ∀ i : Fin (2*(n+1)), completedNativeOperatorCharacteristic (radialPoint k i) ≠ 0)
    (hp : ∀ i : Fin (2*(n+1)), completedNativePositiveHermiteBiehlerCoordinate (radialPoint k i) ≠ 0) :
    inner ℂ (positiveSourceJet (n+1) k x) (positiveSourceJet (n+1) k y)-
      inner ℂ (negativeSourceJet (n+1) k x) (negativeSourceJet (n+1) k y) =
      2*(canonicalCompletedNativeLogDerivativeMoment 0:ℂ)*conj (x 0)*y 0+
        2*nonlinearPairing (n+1) k x y := by
  rw [source_jordan_budget (n+1) k x y hs hp, budget_euler_polarized n k x y hs hf hp]
  ring

/-- Scalar quotient at the OLD one-point source grid. -/
def oneReturn (k : ℕ) : ℂ := completedNativeHermiteBiehlerChiralQuotient
  (canonicalCompletedC3RadialTiltPoint k 0)
def oneDeficit (k : ℕ) : ℝ := 1-Complex.normSq (oneReturn k)
def oneSource (k : ℕ) : RadialIncidentSpan k 1 :=
  radialIncidentVector k 1 (radialDifferenceSourceCoefficients k 1 0)

/-- No coefficient or metric is modified: on one dimension the actual return
is multiplication by its original completed quotient. -/
theorem one_return_apply (k : ℕ) (x : RadialIncidentSpan k 1) :
    radialReturnTransfer k 1 x = oneReturn k • (x : CanonicalCompletedNativeChiralCauchyCarrier) := by
  obtain ⟨c,rfl⟩ := (radialIncidentCoordinates k 1).symm.surjective x
  change radialReturnTransfer k 1 (radialIncidentVector k 1 c) =
    oneReturn k • (radialIncidentVector k 1 c : CanonicalCompletedNativeChiralCauchyCarrier)
  rw [radialReturnTransfer_exact,radialIncidentVector_coe,
    radialReturnedSynthesis_eq_incident_multiply]
  simp only [radialIncidentSynthesis,LinearMap.coe_mk,AddHom.coe_mk,Fin.sum_univ_one]
  simp only [oneReturn,smul_smul,Fin.val_zero]
  congr 1
  ring

/-- The original self-adjoint signed defect, not its positive part. -/
theorem one_defect_apply (k : ℕ) (x : RadialIncidentSpan k 1) :
    radialReturnEnergyDefect k 1 x = (oneDeficit k:ℂ) • x := by
  apply ext_inner_left ℂ
  intro y
  calc
    inner ℂ y (radialReturnEnergyDefect k 1 x) =
        inner ℂ y x-inner ℂ (radialReturnTransfer k 1 y) (radialReturnTransfer k 1 x) :=
      radialReturnEnergyDefect_pairing k 1 y x
    _ = (oneDeficit k:ℂ)*inner ℂ y x := by
      rw [one_return_apply,one_return_apply]
      simp only [inner_smul_left,inner_smul_right]
      change inner ℂ (y:CanonicalCompletedNativeChiralCauchyCarrier) (x:CanonicalCompletedNativeChiralCauchyCarrier)-
        oneReturn k*(conj (oneReturn k)*inner ℂ (y:CanonicalCompletedNativeChiralCauchyCarrier) (x:CanonicalCompletedNativeChiralCauchyCarrier)) =
        (oneDeficit k:ℂ)*inner ℂ (y:CanonicalCompletedNativeChiralCauchyCarrier) (x:CanonicalCompletedNativeChiralCauchyCarrier)
      simp only [oneDeficit,Complex.ofReal_sub,Complex.ofReal_one,Complex.normSq_eq_conj_mul_self]
      ring
    _ = inner ℂ y ((oneDeficit k:ℂ) • x) := (inner_smul_right y x (oneDeficit k:ℂ)).symm

theorem one_storage_scalar (k : ℕ) :
    (storage k (radialDifferenceSourceCoefficients k 1 0) 1).re =
      oneDeficit k*‖oneSource k‖^2 := by
  rw [storage_one_eq_finiteTransfer_energy,one_return_apply,norm_smul]
  change ‖oneSource k‖^2-(‖oneReturn k‖*‖oneSource k‖)^2 = _
  rw [oneDeficit,Complex.normSq_eq_norm_sq]
  ring

/-- Squaring the defect changes the exact source energy by one MORE deficit
factor. This tests B=D, A=D*D on the original complete one-point source. -/
theorem one_squared_defect_energy (k : ℕ) :
    ‖radialReturnEnergyDefect k 1 (oneSource k)‖^2 =
      oneDeficit k*(storage k (radialDifferenceSourceCoefficients k 1 0) 1).re := by
  rw [one_defect_apply,norm_smul,Complex.norm_real,Real.norm_eq_abs, mul_pow,
    sq_abs,one_storage_scalar]
  ring

theorem one_deficit_tendsto_zero : Tendsto oneDeficit atTop (nhds 0) := by
  change Tendsto (fun k => 1-Complex.normSq (oneReturn k)) atTop (nhds 0)
  have hq := hasDerivAt_completedNativeHermiteBiehlerChiralQuotient_zero.continuousAt.tendsto.comp
    (canonicalCompletedC3RadialTiltPoint_tendsto_zero 0)
  have hn := Complex.continuous_normSq.continuousAt.tendsto.comp hq
  have hh := (tendsto_const_nhds (x := (1:ℝ))).sub hn
  simpa only [oneDeficit,oneReturn,completedNativeHermiteBiehlerChiralQuotient_zero,
    Complex.normSq_neg,Complex.normSq_one,sub_self,Function.comp_def] using hh

theorem one_signed_energy_tendsto :
    Tendsto (fun k => (storage k (radialDifferenceSourceCoefficients k 1 0) 1).re)
      atTop (nhds (2*canonicalCompletedNativeLogDerivativeMoment 0)) := by
  have ht := Complex.continuous_re.continuousAt.tendsto.comp
    (projectiveChiralDifferenceJet_pairing_tendsto_coefficient 0 0)
  have he (k : ℕ) :
      (canonicalCompletedNativeProjectiveChiralForm
        (projectiveChiralDifferenceJet k 0) (projectiveChiralDifferenceJet k 0)).re =
        (storage k (radialDifferenceSourceCoefficients k 1 0) 1).re/2 := by
    rw [← radialDifferenceSource_pair k 1 0 (by omega)]
    unfold canonicalCompletedNativeProjectiveChiralForm
    have hs := storage_one_eq_finiteTransfer_energy k 1 (radialDifferenceSourceCoefficients k 1 0)
    rw [radialReturnTransfer_exact,radialIncidentVector_norm] at hs
    rw [hs]
    have hr (a : ℝ) : ((a:ℂ)^2).re=a^2 := by simp [pow_two]
    norm_num [Complex.mul_re,Complex.sub_re,inner_self_eq_norm_sq,hr]
    ring
  simp only [Function.comp_def] at ht
  simp_rw [he] at ht
  have hu := ht.const_mul 2
  have htwo (a : ℝ) : 2*(a/2)=a := by ring
  simpa [htwo,polarizedGreenMomentCoefficient,evenMomentDiagonalCoefficient] using hu

/-- The positive square D*D has zero limiting mass on the SAME source,
while the original signed energy tends to 2 h0. -/
theorem one_squared_energy_tendsto_zero :
    Tendsto (fun k => ‖radialReturnEnergyDefect k 1 (oneSource k)‖^2) atTop (nhds 0) := by
  have ht := one_deficit_tendsto_zero.mul one_signed_energy_tendsto
  simpa only [zero_mul,one_squared_defect_energy] using ht

end
end CarryPositiveSquare
