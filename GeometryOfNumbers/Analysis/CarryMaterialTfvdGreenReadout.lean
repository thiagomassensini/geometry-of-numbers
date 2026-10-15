import GeometryOfNumbers.Analysis.CarryMaterialGeneralTransport
import GeometryOfNumbers.Analysis.BaseTwoPhysicalEdgeTfvdBridge

/-! Bounded REAL readouts of the existing physical-edge TFVD, after genuine
core/direction/depth decoding. Green and trace-return remain distinct. The
material residual and whole-cell boundary return are never discarded.
This is a coordinate/readout bridge, not a canonical moment kernel theorem. -/
namespace GeometryOfNumbers.Analysis
open Geometry BaseTwoCompletion RealCarry C2GlobalGreenBridge GreenFrame.Concrete
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false

def carryMaterialTfvdGreenReadout (eta : ℝ) (i : GlobalC2BranchAddress) (r : Fin 2) :
    MaterialEdgeL2 →L[ℝ] ℝ :=
  (carryVerticalL2Eval i.2.2).comp ((carryVerticalL2WeightedGreen eta).comp
    ((ContinuousLinearMap.fst ℝ CarryVerticalL2 (ℝ × ℝ)).comp
      (baseTwoPhysicalTfvdChannel eta i.1 i.2.1 r)))

def carryMaterialTfvdReturnReadout (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (i : GlobalC2BranchAddress) (r : Fin 2) : MaterialEdgeL2 →L[ℝ] ℝ :=
  (carryVerticalL2Eval i.2.2).comp ((carryWeightedVerticalReturn eta h0.le h1).comp
    ((ContinuousLinearMap.snd ℝ CarryVerticalL2 (ℝ × ℝ)).comp
      (baseTwoPhysicalTfvdChannel eta i.1 i.2.1 r)))

theorem carryMaterialTfvd_coordinate (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (i : GlobalC2BranchAddress) (r : Fin 2) (g : MaterialEdgeL2) :
    carryMaterialTfvdGreenReadout eta i r g + carryMaterialTfvdReturnReadout eta h0 h1 i r g =
      baseTwoPhysicalEdgeC2State g i r := by
  have h := c2FiberTfvdSynthesis_analysis eta h0 h1 (baseTwoPhysicalEdgeC2State g)
  exact congrArg (fun z : C2RealVerticalChannels => z i.1 i.2.1 r i.2.2) h

theorem carryMaterialTfvdGreen_hasDerivAt (eta t : ℝ) (i : GlobalC2BranchAddress) (r : Fin 2) :
    HasDerivAt (fun s => carryMaterialTfvdGreenReadout eta i r (baseTwoCompletedMaterialGradientL2 s))
      (carryMaterialTfvdGreenReadout eta i r (-Complex.I • baseTwoCompletedMaterialClockL2 t)) t :=
  (carryMaterialTfvdGreenReadout eta i r).hasFDerivAt.comp_hasDerivAt t
    (baseTwoCompletedMaterialGradientL2_hasDerivAt_clock t)

theorem carryMaterialTfvdReturn_hasDerivAt (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (t : ℝ) (i : GlobalC2BranchAddress) (r : Fin 2) :
    HasDerivAt (fun s => carryMaterialTfvdReturnReadout eta h0 h1 i r (baseTwoCompletedMaterialGradientL2 s))
      (carryMaterialTfvdReturnReadout eta h0 h1 i r (-Complex.I • baseTwoCompletedMaterialClockL2 t)) t :=
  (carryMaterialTfvdReturnReadout eta h0 h1 i r).hasFDerivAt.comp_hasDerivAt t
    (baseTwoCompletedMaterialGradientL2_hasDerivAt_clock t)

/-- The trace is not dropped or treated as an orthogonal correction to Green. -/
theorem carryMaterialTfvd_return_formula (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (i : GlobalC2BranchAddress) (r : Fin 2) (g : MaterialEdgeL2) :
    carryMaterialTfvdReturnReadout eta h0 h1 i r g =
      eta ^ i.2.2 * (baseTwoPhysicalEdgeC2State g (i.1, (i.2.1, 0)) r +
        (i.2.2 : ℝ) * (eta⁻¹ * baseTwoPhysicalEdgeC2State g (i.1, (i.2.1, 1)) r -
          baseTwoPhysicalEdgeC2State g (i.1, (i.2.1, 0)) r)) := by
  change carryWeightedVerticalReturn eta h0.le h1
    (carryWeightedVerticalTrace eta (c2BranchVerticalCoordinate i.1 i.2.1 r
      (baseTwoPhysicalEdgeC2State g))) i.2.2 = _
  rw [carryWeightedVerticalReturn_apply, carryWeightedVerticalTrace_apply]
  rfl

theorem carryMaterialTfvd_green_zero (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (r : Fin 2) (g : MaterialEdgeL2) :
    carryMaterialTfvdGreenReadout eta (c2UnitOddCore, (0, 0)) r g = 0 := by
  have h := carryMaterialTfvd_coordinate eta h0 h1 (c2UnitOddCore, (0, 0)) r g
  rw [carryMaterialTfvd_return_formula] at h
  simp only [pow_zero, Nat.cast_zero, zero_mul, add_zero, one_mul] at h
  linarith

/-- First coordinate where the causal Green interior can contribute. -/
theorem carryMaterialTfvd_green_two (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (r : Fin 2) (g : MaterialEdgeL2) :
    carryMaterialTfvdGreenReadout eta (c2UnitOddCore, (0, 2)) r g =
      baseTwoPhysicalEdgeC2State g (c2UnitOddCore, (0, 2)) r -
        2 * eta * baseTwoPhysicalEdgeC2State g (c2UnitOddCore, (0, 1)) r +
        eta ^ 2 * baseTwoPhysicalEdgeC2State g (c2UnitOddCore, (0, 0)) r := by
  have h := carryMaterialTfvd_coordinate eta h0 h1 (c2UnitOddCore, (0, 2)) r g
  calc
    _ = baseTwoPhysicalEdgeC2State g (c2UnitOddCore, (0, 2)) r -
        carryMaterialTfvdReturnReadout eta h0 h1 (c2UnitOddCore, (0, 2)) r g := by linarith
    _ = _ := by
      rw [carryMaterialTfvd_return_formula]
      norm_num only [Nat.cast_ofNat]
      field_simp
      ring

theorem carryMaterialTfvd_edge (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (e : BaseTwoPhysicalEdge) (r : Fin 2) (g : MaterialEdgeL2) :
    carryMaterialTfvdGreenReadout eta (baseTwoPhysicalEdgeC2Address e) r g +
        carryMaterialTfvdReturnReadout eta h0 h1 (baseTwoPhysicalEdgeC2Address e) r g =
      baseTwoMaterialEdgeRealification (g (baseTwoPhysicalEdgeIndex e)) r := by
  rw [carryMaterialTfvd_coordinate, baseTwoPhysicalEdgeC2State_apply_edge]

/-- All four ordered Green/trace-return crossings, with independent inputs.
Complex notation packages the two real readouts only AFTER their synthesis. -/
theorem carryMaterialTfvd_edge_pairing (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (e f : BaseTwoPhysicalEdge) (g h : MaterialEdgeL2) :
    let G := fun e g => Complex.mk
      (carryMaterialTfvdGreenReadout eta (baseTwoPhysicalEdgeC2Address e) 0 g)
      (carryMaterialTfvdGreenReadout eta (baseTwoPhysicalEdgeC2Address e) 1 g)
    let R := fun e g => Complex.mk
      (carryMaterialTfvdReturnReadout eta h0 h1 (baseTwoPhysicalEdgeC2Address e) 0 g)
      (carryMaterialTfvdReturnReadout eta h0 h1 (baseTwoPhysicalEdgeC2Address e) 1 g)
    conj (g (baseTwoPhysicalEdgeIndex e)) * h (baseTwoPhysicalEdgeIndex f) =
      conj (G e g) * G f h + conj (G e g) * R f h +
        conj (R e g) * G f h + conj (R e g) * R f h := by
  dsimp only
  have he : g (baseTwoPhysicalEdgeIndex e) =
      Complex.mk (carryMaterialTfvdGreenReadout eta (baseTwoPhysicalEdgeC2Address e) 0 g)
        (carryMaterialTfvdGreenReadout eta (baseTwoPhysicalEdgeC2Address e) 1 g) +
      Complex.mk (carryMaterialTfvdReturnReadout eta h0 h1 (baseTwoPhysicalEdgeC2Address e) 0 g)
        (carryMaterialTfvdReturnReadout eta h0 h1 (baseTwoPhysicalEdgeC2Address e) 1 g) := by
    apply Complex.ext
    · exact (carryMaterialTfvd_edge eta h0 h1 e 0 g).symm
    · exact (carryMaterialTfvd_edge eta h0 h1 e 1 g).symm
  have hf : h (baseTwoPhysicalEdgeIndex f) =
      Complex.mk (carryMaterialTfvdGreenReadout eta (baseTwoPhysicalEdgeC2Address f) 0 h)
        (carryMaterialTfvdGreenReadout eta (baseTwoPhysicalEdgeC2Address f) 1 h) +
      Complex.mk (carryMaterialTfvdReturnReadout eta h0 h1 (baseTwoPhysicalEdgeC2Address f) 0 h)
        (carryMaterialTfvdReturnReadout eta h0 h1 (baseTwoPhysicalEdgeC2Address f) 1 h) := by
    apply Complex.ext
    · exact (carryMaterialTfvd_edge eta h0 h1 f 0 h).symm
    · exact (carryMaterialTfvd_edge eta h0 h1 f 1 h).symm
  rw [he, hf]
  simp only [map_add]
  ring

/-- Actual source action, not an assumed kernel equality. -/
theorem carryMaterialTfvd_edge_source (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (e : BaseTwoPhysicalEdge) (r : Fin 2) (t : ℝ) :
    carryMaterialTfvdGreenReadout eta (baseTwoPhysicalEdgeC2Address e) r
        (baseTwoCompletedMaterialGradientL2 t) +
      carryMaterialTfvdReturnReadout eta h0 h1 (baseTwoPhysicalEdgeC2Address e) r
        (baseTwoCompletedMaterialGradientL2 t) =
      baseTwoMaterialEdgeRealification (criticalMaterialGradient t (baseTwoPhysicalEdgeIndex e)) r := by
  simpa only [baseTwoCompletedMaterialGradientL2_apply, baseTwoCompletedMaterialGradient_apply] using
    carryMaterialTfvd_edge eta h0 h1 e r (baseTwoCompletedMaterialGradientL2 t)

/-- The physical depth coordinate j is depth minus two, not the edge index. -/
theorem carryMaterialTfvd72_addresses :
    (baseTwoPhysicalEdgeC2Address (19, 1)).1.val = 5 ∧
    (baseTwoPhysicalEdgeC2Address (19, 1)).2 = (1, 2) ∧
    baseTwoPhysicalEdgeC2Address (15, 0) = (c2UnitOddCore, (0, 4)) := by
  have hr : baseTwoPhysicalEdgeC2Address (19, 1) =
      (⟨5, by decide, by decide⟩, (1, 2)) := by
    apply globalC2MaterialAddress_injective
    rw [baseTwoPhysicalEdgeC2Address_material]
    rfl
  have hl : baseTwoPhysicalEdgeC2Address (15, 0) = (c2UnitOddCore, (0, 4)) := by
    apply globalC2MaterialAddress_injective
    rw [baseTwoPhysicalEdgeC2Address_material]
    rfl
  exact ⟨congrArg (fun i : GlobalC2BranchAddress => i.1.val) hr,
    congrArg Prod.snd hr, hl⟩

/-- The radius transport correction is recovered in the existing TFVD,
with both Green and return pieces in each real quadrature. -/
theorem carryMaterialTfvd72_correction (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (r : Fin 2) (t : ℝ) :
    let g := baseTwoCompletedMaterialGradientL2 t
    let i := baseTwoPhysicalEdgeC2Address (19, 1)
    let j := baseTwoPhysicalEdgeC2Address (15, 0)
    carryMaterialTfvdGreenReadout eta i r g + carryMaterialTfvdReturnReadout eta h0 h1 i r g -
      (carryMaterialTfvdGreenReadout eta j r g + carryMaterialTfvdReturnReadout eta h0 h1 j r g) =
      baseTwoMaterialEdgeRealification (criticalMaterialGradient t 79 - criticalMaterialGradient t 62) r := by
  dsimp only
  rw [carryMaterialTfvd_edge_source, carryMaterialTfvd_edge_source, map_sub]
  rfl

/-- Explicit zeroth and first nontrivial interior sample on the unit/left
fiber. This is calibration against the material source, not canonical jets. -/
theorem carryMaterialTfvd_unit_samples (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (r : Fin 2) (t : ℝ) :
    let g := baseTwoCompletedMaterialGradientL2 t
    (carryMaterialTfvdGreenReadout eta (c2UnitOddCore, (0, 0)) r g +
      carryMaterialTfvdReturnReadout eta h0 h1 (c2UnitOddCore, (0, 0)) r g =
        baseTwoMaterialEdgeRealification (criticalMaterialGradient t 2) r) ∧
    (carryMaterialTfvdGreenReadout eta (c2UnitOddCore, (0, 2)) r g +
      carryMaterialTfvdReturnReadout eta h0 h1 (c2UnitOddCore, (0, 2)) r g =
        baseTwoMaterialEdgeRealification (criticalMaterialGradient t 14) r) := by
  have ha : baseTwoPhysicalEdgeC2Address (0, 0) = (c2UnitOddCore, (0, 0)) := by
    apply globalC2MaterialAddress_injective
    rw [baseTwoPhysicalEdgeC2Address_material]
    rfl
  have hb : baseTwoPhysicalEdgeC2Address (3, 0) = (c2UnitOddCore, (0, 2)) := by
    apply globalC2MaterialAddress_injective
    rw [baseTwoPhysicalEdgeC2Address_material]
    rfl
  constructor
  · simpa only [ha, show baseTwoPhysicalEdgeIndex (0, 0) = 2 from rfl] using
      carryMaterialTfvd_edge_source eta h0 h1 (0, 0) r t
  · simpa only [hb, show baseTwoPhysicalEdgeIndex (3, 0) = 14 from rfl] using
      carryMaterialTfvd_edge_source eta h0 h1 (3, 0) r t

/-- Zeroth/first-interior crossing on the ACTUAL source, with independent
phases and independent quadrature labels. -/
theorem carryMaterialTfvd_unit_cross (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (r s : Fin 2) (t u : ℝ) :
    let g := baseTwoCompletedMaterialGradientL2
    (carryMaterialTfvdGreenReadout eta (c2UnitOddCore, (0, 0)) r (g t) +
      carryMaterialTfvdReturnReadout eta h0 h1 (c2UnitOddCore, (0, 0)) r (g t)) *
    (carryMaterialTfvdGreenReadout eta (c2UnitOddCore, (0, 2)) s (g u) +
      carryMaterialTfvdReturnReadout eta h0 h1 (c2UnitOddCore, (0, 2)) s (g u)) =
    baseTwoMaterialEdgeRealification (criticalMaterialGradient t 2) r *
      baseTwoMaterialEdgeRealification (criticalMaterialGradient u 14) s := by
  dsimp only
  rw [(carryMaterialTfvd_unit_samples eta h0 h1 r t).1,
    (carryMaterialTfvd_unit_samples eta h0 h1 s u).2]

/-- Source-specific obstruction to omitting the trace-return: the Green
coordinate is zero here but the actual return is strictly negative. -/
theorem carryMaterialTfvd_return_zero_negative (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    carryMaterialTfvdReturnReadout eta h0 h1 (c2UnitOddCore, (0, 0)) 0
      (baseTwoCompletedMaterialGradientL2 0) < 0 := by
  have h := (carryMaterialTfvd_unit_samples eta h0 h1 0 0).1
  rw [carryMaterialTfvd_green_zero eta h0 h1] at h
  change 0 + carryMaterialTfvdReturnReadout eta h0 h1 (c2UnitOddCore, (0, 0)) 0
    (baseTwoCompletedMaterialGradientL2 0) = (criticalMaterialGradient 0 2).re at h
  have hh : carryMaterialTfvdReturnReadout eta h0 h1 (c2UnitOddCore, (0, 0)) 0
      (baseTwoCompletedMaterialGradientL2 0) = (criticalMaterialGradient 0 2).re := by
    simpa only [zero_add] using h
  rw [hh]
  norm_num [criticalMaterialGradient, criticalMaterialSample]
  have hs := Real.sqrt_nonneg (3 : ℝ)
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  nlinarith

/-- Polarization upgrades the EXISTING physical/residual energy split.
No assumption that local camera energies determine a global Gram is used. -/
theorem carryMaterial_physical_residual_pairing (g h : MaterialEdgeL2) :
    inner ℝ g h = inner ℝ (baseTwoPhysicalEdgeC2State g) (baseTwoPhysicalEdgeC2State h) +
      inner ℝ (baseTwoResidualEdgeProjection g) (baseTwoResidualEdgeProjection h) := by
  have hg := baseTwoPhysicalC2Residual_norm_sq g
  have hh := baseTwoPhysicalC2Residual_norm_sq h
  have hs := baseTwoPhysicalC2Residual_norm_sq (g + h)
  rw [map_add, map_add] at hs
  simp only [norm_add_sq_real] at hs
  linarith

/-- General-radius corrections retain BOTH support sectors. Each physical
coordinate has the Green+trace reconstruction above; no formula silently
drops the residual indices 0 or 1 modulo four. -/
theorem carryMaterialRadiusCorrection_residual_ledger (c h H : ℕ)
    (y : BaseTwoCompletedBoundaryHilbertCarrier) :
    carryMaterialRadiusCorrection c h H y =
      ((∑ p ∈ Finset.Ico (c + h) (c + H), baseTwoPhysicalEdgeProjection y.snd.fst (p - 1)) -
        ∑ p ∈ Finset.Ico (c - H) (c - h), baseTwoPhysicalEdgeProjection y.snd.fst (p - 1)) +
      ((∑ p ∈ Finset.Ico (c + h) (c + H), baseTwoResidualEdgeProjection y.snd.fst (p - 1)) -
        ∑ p ∈ Finset.Ico (c - H) (c - h), baseTwoResidualEdgeProjection y.snd.fst (p - 1)) := by
  have hg (n : ℕ) : y.snd.fst n =
      baseTwoPhysicalEdgeProjection y.snd.fst n + baseTwoResidualEdgeProjection y.snd.fst n :=
    (congrArg (fun g : MaterialEdgeL2 => g n) (baseTwoPhysicalResidual_reconstruction y.snd.fst)).symm
  simp only [carryMaterialRadiusCorrection, sub_apply, carryMaterialIntervalReadout_apply]
  simp_rw [hg, Finset.sum_add_distrib]
  ring

theorem carryMaterial_complete_real_pairing (t u : ℝ) :
    let g := baseTwoCompletedMaterialGradientL2
    inner ℝ (baseTwoCompletedBoundaryHilbertState t) (baseTwoCompletedBoundaryHilbertState u) =
      inner ℝ (criticalMaterialSample t 1) (criticalMaterialSample u 1) +
      inner ℝ (baseTwoPhysicalOrdinaryC2State t) (baseTwoPhysicalOrdinaryC2State u) +
      inner ℝ (baseTwoResidualEdgeProjection (g t)) (baseTwoResidualEdgeProjection (g u)) +
      inner ℝ (baseTwoCompletedBoundaryValue t) (baseTwoCompletedBoundaryValue u) := by
  dsimp only
  change inner ℝ (criticalMaterialSample t 1) (criticalMaterialSample u 1) +
    (inner ℝ (baseTwoCompletedMaterialGradientL2 t) (baseTwoCompletedMaterialGradientL2 u) +
      inner ℝ (baseTwoCompletedBoundaryValue t) (baseTwoCompletedBoundaryValue u)) = _
  rw [carryMaterial_physical_residual_pairing]
  simp only [baseTwoPhysicalOrdinaryC2State]
  ring

end
end GeometryOfNumbers.Analysis
