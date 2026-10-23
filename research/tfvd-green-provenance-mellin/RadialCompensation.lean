import CompleteLedger

namespace CarryGreenProvenance
open CarryFourLeg CarryCameraTail CarryMaterialTheta CarrySelfAdjointOperator
open CPFormal.Analytic.Cp NativeCarryC3Crosswalk NativeCarrySpectralWeyl.Boundary
noncomputable section
set_option autoImplicit false

/-- Explicit coefficient of the ORIGINAL radial normalization; no new
source weight or metric is selected. -/
theorem material_port_coordinates (N : ℕ) (i : Fin N) {s : ℂ} (hs : 0 < s.re) :
    ((materialGreenPort N s).1 i, (materialGreenPort N s).2 i) =
      ((((3 : ℝ)^(-criticalDisplacement s.re) : ℝ) : ℂ) *
        positiveDirichletGradient s i.val, positiveDirichletGradient s i.val) := by
  rw [material_green_port_eq N hs]
  simp only [finiteC3GenuineBracketGreenBoundaryPair_fst_apply,
    finiteC3GenuineBracketGreenBoundaryPair_snd_apply,
    phaseNormalizedCpGenuineGreenGradient_eq_phaseNormalizedCpBlockGradient
      3 (by norm_num), phaseNormalizedCpBlockGradient_eq_radial_mul 3 (by norm_num)]
  norm_num only [Nat.cast_ofNat]

/-- Two independent parameters: both radial gains survive in the edge.
This coefficient has no prescribed sign. -/
theorem green_edge_radial (N : ℕ) (i : Fin N) {s t : ℂ}
    (hs : 0 < s.re) (ht : 0 < t.re) :
    finiteC3GreenPortEdge (materialGreenPort N s) (materialGreenPort N t) i =
      ((((3 : ℝ)^(-criticalDisplacement t.re) -
          (3 : ℝ)^(-criticalDisplacement s.re) : ℝ) : ℂ)) *
        (starRingEnd ℂ) (positiveDirichletGradient s i.val) *
        positiveDirichletGradient t i.val := by
  have hsf := congrArg Prod.fst (material_port_coordinates N i hs)
  have hss := congrArg Prod.snd (material_port_coordinates N i hs)
  have htf := congrArg Prod.fst (material_port_coordinates N i ht)
  have hts := congrArg Prod.snd (material_port_coordinates N i ht)
  dsimp only at hsf hss htf hts
  unfold finiteC3GreenPortEdge
  rw [hsf, hss, htf, hts]
  simp only [map_mul, Complex.conj_ofReal, Complex.ofReal_sub]
  ring

/-- The dormant term is the oriented THIRD residue, not an erased zero
coordinate. Its formula is derived with the actual radial phases. -/
theorem dormant_compensation_radial (M : ℕ) (m : Fin M) {z w : ℂ}
    (hz1 : z.re < 1) (hw : 0 < w.re) :
    (heatBlockProvenance M z w m).dormantGreenCompensation =
      -(((((3 : ℝ)^(criticalDisplacement z.re) -
          (3 : ℝ)^(-criticalDisplacement w.re) : ℝ) : ℂ)) *
        (starRingEnd ℂ) (positiveDirichletGradient w (finProdFinEquiv (m, (2 : Fin 3))).val) *
        positiveDirichletGradient (reflectedParameter z)
          (finProdFinEquiv (m, (2 : Fin 3))).val) := by
  change -finiteC3GreenPortEdge _ _ _ = _
  rw [green_edge_radial _ _ hw (reflected_re_pos hz1),
    criticalDisplacement_reflectedParameter]
  simp only [neg_neg]

/-- On the critical line both legs coincide coordinatewise. The state is
not thereby a zero vector: the conclusion concerns a skew-Hermitian form. -/
theorem critical_port_legs_equal (N : ℕ) {s : ℂ} (hs : s.re = 1/2) :
    (materialGreenPort N s).1 = (materialGreenPort N s).2 := by
  have hp : 0 < s.re := by rw [hs]; norm_num
  ext i
  have h := material_port_coordinates N i hp
  have hf := congrArg Prod.fst h
  have hh := congrArg Prod.snd h
  dsimp only at hf hh
  rw [hf, hh]
  simp [criticalDisplacement, hs]

theorem critical_green_edge_zero (N : ℕ) (i : Fin N) {s t : ℂ}
    (hs : s.re = 1/2) (ht : t.re = 1/2) :
    finiteC3GreenPortEdge (materialGreenPort N s) (materialGreenPort N t) i = 0 := by
  unfold finiteC3GreenPortEdge
  rw [critical_port_legs_equal N hs, critical_port_legs_equal N ht, sub_self]

theorem critical_green_form_zero (N : ℕ) {s t : ℂ}
    (hs : s.re = 1/2) (ht : t.re = 1/2) :
    greenForm (𝕜 := ℂ) (materialGreenPort N s) (materialGreenPort N t) = 0 := by
  rw [greenForm_eq_sum_finiteC3GreenPortEdge]
  simp_rw [critical_green_edge_zero N _ hs ht]
  simp

theorem critical_dormant_compensation_zero (M : ℕ) (m : Fin M) {z w : ℂ}
    (hz : z.re = 1/2) (hw : w.re = 1/2) :
    (heatBlockProvenance M z w m).dormantGreenCompensation = 0 := by
  have hr : (reflectedParameter z).re = 1/2 := by rw [reflectedParameter_re, hz]; norm_num
  change -finiteC3GreenPortEdge _ _ _ = 0
  rw [critical_green_edge_zero _ _ hw hr, neg_zero]

/-- No information is discarded: the original full Wronskian on the
critical product is carried by the FOUR correction fields. Vanishing of
the finite radial Green term does not make those corrections vanish. -/
theorem critical_wronskian_in_ledger (M : ℕ) {z w : ℂ}
    (hz : z.re = 1/2) (hw : w.re = 1/2) :
    canonicalCompletedC3RawMixedWronskian z w =
      (heatLedger M z w).greenProvenance + (heatLedger M z w).crossProvenance +
      (heatLedger M z w).readoutResidual + (heatLedger M z w).completion := by
  have hz0 : 0 < z.re := by rw [hz]; norm_num
  have hz1 : z.re < 1 := by rw [hz]; norm_num
  have hw0 : 0 < w.re := by rw [hw]; norm_num
  have hr : (reflectedParameter z).re = 1/2 := by rw [reflectedParameter_re, hz]; norm_num
  have h := native_wronskian_full_mellin M hz0 hz1 hw0
  rw [critical_green_form_zero _ hw hr, zero_add] at h
  exact h

end
end CarryGreenProvenance
