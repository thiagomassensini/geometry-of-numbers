import PhysicalLimits

/-! Reassemble the already extracted central source channel with the physical
residual vectors. The product norm is inherited; its coefficient is forced
by the old source axis and positive central scale. This is a FINITE block. -/
namespace CarryCorrectedGreenPorts
open GeometryOfNumbers.Analysis CarrySelfAdjointOperator
open CarrySelfAdjointOperator.ChiralReturn
open CarryMaterialResponseComparison CarryMaterialMixedSchurComparison
open Filter
open scoped BigOperators InnerProductSpace ComplexConjugate Topology
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- Coefficient of the existing extracted central channel, not a fitted
constant: sqrt(a0) times the actual source's central elimination weight. -/
def sourceCentralFeature (p : ℕ) : ℂ :=
  (Real.sqrt carryMaterialResponseScale : ℂ)*sourceCenterWeight p

theorem sourceCentralFeature_pairing (p q : ℕ) :
    conj (sourceCentralFeature p)*sourceCentralFeature q =
      completedNativeGreenResponseTaylorCoefficient (p+1)*
        completedNativeGreenResponseTaylorCoefficient (q+1)/
          (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := by
  have hs : (Real.sqrt carryMaterialResponseScale : ℂ)*
      (Real.sqrt carryMaterialResponseScale : ℂ) = (carryMaterialResponseScale : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt material_scale_pos.le]
  calc
    _ = (carryMaterialResponseScale : ℂ)*sourceCenterWeight p*sourceCenterWeight q := by
      simp only [sourceCentralFeature, map_mul, Complex.conj_ofReal, sourceCenterWeight_conj]
      rw [show (Real.sqrt carryMaterialResponseScale : ℂ)*sourceCenterWeight p*
          ((Real.sqrt carryMaterialResponseScale : ℂ)*sourceCenterWeight q) =
        ((Real.sqrt carryMaterialResponseScale : ℂ)*(Real.sqrt carryMaterialResponseScale : ℂ))*
          sourceCenterWeight p*sourceCenterWeight q by ring, hs]
    _ = _ := by
      rw [sourceCenterWeight_eq_coefficient, sourceCenterWeight_eq_coefficient, material_scale_eq]
      have hn : (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) ≠ 0 := by
        exact_mod_cast canonicalCompletedNativeLogDerivativeMoment_zero_pos.ne'
      field_simp

/-- Reassembly of full canonical coefficients is an identity of the actual
source, before any finite positive realization is supplied. -/
theorem sourceCentralFeature_add_residual (p q : ℕ) :
    conj (sourceCentralFeature p)*sourceCentralFeature q+
      carryKernelJet (fun t u => (carryMaterialRealResidual t u : ℂ)) p q =
        polarizedGreenMomentCoefficient canonicalCompletedNativeLogDerivativeMoment p q := by
  rw [sourceCentralFeature_pairing, material_residual_complex_jet_source,
    ← completedNativeGreenResponseTaylorCoefficient_succ_eq_polarized]
  ring

abbrev FullSourceCarrier := WithLp 2 (ℂ × CanonicalCompletedNativeChiralCauchyCarrier)

/-- The same direct-sum construction used upstream for the extracted source
feature plus residual; no target Gram factorization defines these vectors. -/
def fullSourceJet {N : ℕ}
    (v : Fin (N+1) → CanonicalCompletedNativeChiralCauchyCarrier) (a : Fin (N+1)) :
    FullSourceCarrier := WithLp.toLp 2 (sourceCentralFeature a.val, v a)

theorem fullSourceJet_pairing {N : ℕ}
    (v : Fin (N+1) → CanonicalCompletedNativeChiralCauchyCarrier)
    (hv : ∀ a b, inner ℂ (v a) (v b) =
      carryKernelJet (fun t u => (carryMaterialRealResidual t u : ℂ)) a.val b.val)
    (a b : Fin (N+1)) :
    inner ℂ (fullSourceJet v a) (fullSourceJet v b) =
      polarizedGreenMomentCoefficient canonicalCompletedNativeLogDerivativeMoment a.val b.val := by
  change inner ℂ (WithLp.toLp 2 (sourceCentralFeature a.val, v a))
    (WithLp.toLp 2 (sourceCentralFeature b.val, v b)) = _
  rw [WithLp.prod_inner_apply]
  change sourceCentralFeature b.val*conj (sourceCentralFeature a.val)+inner ℂ (v a) (v b) = _
  rw [hv a b, mul_comm (sourceCentralFeature b.val)]
  exact sourceCentralFeature_add_residual a.val b.val

/-- Unconditional exact FINITE canonical jet Gram, constructed from limits
of the original return-energy ports and the already extracted source feature.
There is no claim of an infinite compatible family or a new HP certificate. -/
theorem canonical_seven_source_realization :
    ∃ v : Fin 7 → CanonicalCompletedNativeChiralCauchyCarrier,
      (∀ a, v a ∈ RadialIncidentSpan 0 7) ∧
      (∀ a b, inner ℂ (fullSourceJet v a) (fullSourceJet v b) =
        polarizedGreenMomentCoefficient canonicalCompletedNativeLogDerivativeMoment a.val b.val) := by
  obtain ⟨v,hmem,hv⟩ := correctedGreen_seven_physical_realization 1 (by norm_num)
  refine ⟨v,hmem,?_⟩
  apply fullSourceJet_pairing v
  intro a b
  rw [hv a b, material_valve_confluent_jet 1 (by norm_num)]

/-- Real metric and J-form of the SAME physical vectors. The zero J-form is
proved only at the exact canonical limit; finite-cutoff crosses were retained. -/
theorem correctedGreen_seven_real_quadrature_realization :
    ∃ v : Fin 7 → CanonicalCompletedNativeChiralCauchyCarrier,
      (∀ a, v a ∈ RadialIncidentSpan 0 7) ∧
      (∀ a b, (Inner.rclikeToReal ℂ CanonicalCompletedNativeChiralCauchyCarrier).inner
        (v a) (v b) = carryMaterialResidualJet a.val b.val) ∧
      (∀ a b, (Inner.rclikeToReal ℂ CanonicalCompletedNativeChiralCauchyCarrier).inner
        (v a) (Complex.I • v b) = 0) := by
  obtain ⟨v,hmem,hv⟩ := correctedGreen_seven_physical_realization 1 (by norm_num)
  have hp (a b : Fin 7) : inner ℂ (v a) (v b) =
      (carryMaterialResidualJet a.val b.val : ℂ) := by
    rw [hv a b, material_valve_confluent_jet 1 (by norm_num), ← residualJet_eq_real]
  refine ⟨v,hmem,?_,?_⟩
  · intro a b
    change (inner ℂ (v a) (v b)).re = _
    rw [hp]
    rfl
  · intro a b
    change (inner ℂ (v a) (Complex.I • v b)).re = _
    rw [inner_smul_right, hp]
    simp [Complex.mul_re]

end
end CarryCorrectedGreenPorts
