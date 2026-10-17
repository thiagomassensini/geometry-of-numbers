import GeometryOfNumbers.Analysis.CarryMaterialTfvdGreenReadout
import GeometryOfNumbers.Analysis.RealDiscreteProjectiveReconstruction

/-! # The actual physical TFVD fibers in the projective valve

The inverse amplitude gauge is pointwise; no bounded inverse on l2 is asserted.
Every core, direction, depth and real quadrature keeps its own boundary and
normalized mass. Seed, residual edges and GLOBAL return remain separate.
The encoding is nonlinear and its target is not given a new Hilbert metric.
-/
namespace GeometryOfNumbers.Analysis
open BaseTwoCompletion RealCarry DiscreteValve DiscreteProjective ProjectiveValve
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Undo only the existing vertical amplitude gauge, after incidence decoding. -/
def carryMaterialProjectiveProfile (eta : ℝ) (g : MaterialEdgeL2)
    (m : PositiveOddCore) (a : C2BranchDirection) (r : Fin 2) (j : ℕ) : ℝ :=
  (eta ^ j)⁻¹ * baseTwoPhysicalEdgeC2State g (m, (a, j)) r

/-- The curvature is caused by the actual fiber, before applying the valve. -/
def carryMaterialProjectiveCurvature (eta : ℝ) (g : MaterialEdgeL2)
    (m : PositiveOddCore) (a : C2BranchDirection) (r : Fin 2) : PowerSeries ℝ :=
  ProjectiveDepth.toProjective (PowerSeries.mk
    (bracket (carryMaterialProjectiveProfile eta g m a r)))

def carryMaterialProjectiveFiberData (eta : ℝ) (g : MaterialEdgeL2)
    (m : PositiveOddCore) (a : C2BranchDirection) (r : Fin 2) : ReconstructionData ℝ :=
  encode (carryMaterialProjectiveProfile eta g m a r)

theorem carryMaterialProjective_mass (eta : ℝ) (g : MaterialEdgeL2)
    (m : PositiveOddCore) (a : C2BranchDirection) (r : Fin 2) :
    (carryMaterialProjectiveFiberData eta g m a r).projectiveMass.1 =
      projectiveValveMass (carryMaterialProjectiveCurvature eta g m a r) := rfl

theorem carryMaterialProjective_curvature (eta : ℝ) (g : MaterialEdgeL2)
    (m : PositiveOddCore) (a : C2BranchDirection) (r : Fin 2) :
    projectiveValveCurvature
        (carryMaterialProjectiveFiberData eta g m a r).projectiveMass.1 =
      carryMaterialProjectiveCurvature eta g m a r :=
  projectiveValveCurvature_stateMass _

/-- The actual additive source channels become a product of scalar masses.
This statement does not turn the nonlinear mass map into a Hilbert isometry. -/
theorem carryMaterialProjective_curvature_add (eta : ℝ) (g h : MaterialEdgeL2)
    (m : PositiveOddCore) (a : C2BranchDirection) (r : Fin 2) :
    carryMaterialProjectiveCurvature eta (g + h) m a r =
      carryMaterialProjectiveCurvature eta g m a r +
        carryMaterialProjectiveCurvature eta h m a r := by
  unfold carryMaterialProjectiveCurvature
  rw [← ProjectiveDepth.toProjective_add]
  congr 1
  ext j
  simp only [map_add, PowerSeries.coeff_mk, bracket, nsmul_eq_mul,
    carryMaterialProjectiveProfile]
  change (eta ^ (j+2))⁻¹ *
      (baseTwoPhysicalEdgeC2State g (m, (a, j+2)) r + baseTwoPhysicalEdgeC2State h (m, (a, j+2)) r) -
      2 * ((eta ^ (j+1))⁻¹ *
      (baseTwoPhysicalEdgeC2State g (m, (a, j+1)) r + baseTwoPhysicalEdgeC2State h (m, (a, j+1)) r)) +
      (eta ^ j)⁻¹ *
      (baseTwoPhysicalEdgeC2State g (m, (a, j)) r + baseTwoPhysicalEdgeC2State h (m, (a, j)) r) = _
  ring

theorem carryMaterialProjective_mass_add (eta : ℝ) (g h : MaterialEdgeL2)
    (m : PositiveOddCore) (a : C2BranchDirection) (r : Fin 2) :
    (carryMaterialProjectiveFiberData eta (g + h) m a r).projectiveMass.1 =
      (carryMaterialProjectiveFiberData eta g m a r).projectiveMass.1 *
        (carryMaterialProjectiveFiberData eta h m a r).projectiveMass.1 := by
  simp only [carryMaterialProjective_mass, carryMaterialProjective_curvature_add,
    projectiveValveMass_add]

/-- Depth coefficient zero is a second difference of material edge readings;
it is not a norm or a height jet. -/
theorem carryMaterialProjective_curvature_zero (eta : ℝ) (g : MaterialEdgeL2)
    (m : PositiveOddCore) (a : C2BranchDirection) (r : Fin 2) :
    PowerSeries.constantCoeff (carryMaterialProjectiveCurvature eta g m a r) =
      (eta ^ 2)⁻¹ * baseTwoPhysicalEdgeC2State g (m, (a, 2)) r -
        2 * (eta⁻¹ * baseTwoPhysicalEdgeC2State g (m, (a, 1)) r) +
          baseTwoPhysicalEdgeC2State g (m, (a, 0)) r := by
  rw [carryMaterialProjectiveCurvature, ProjectiveDepth.constantCoeff_toProjective,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
  simp only [bracket, carryMaterialProjectiveProfile, nsmul_eq_mul,
    zero_add, pow_one, pow_zero, inv_one, one_mul, Nat.cast_ofNat]

theorem carryMaterialProjective_regauge (eta : ℝ) (heta : eta ≠ 0)
    (g : MaterialEdgeL2) (m : PositiveOddCore) (a : C2BranchDirection)
    (r : Fin 2) (j : ℕ) :
    eta ^ j * carryMaterialProjectiveProfile eta g m a r j =
      baseTwoPhysicalEdgeC2State g (m, (a, j)) r := by
  unfold carryMaterialProjectiveProfile
  field_simp

/-- Both original TFVD trace coordinates are retained in the valve encoding. -/
theorem carryMaterialProjective_boundary (eta : ℝ) (g : MaterialEdgeL2)
    (m : PositiveOddCore) (a : C2BranchDirection) (r : Fin 2) :
    ((carryMaterialProjectiveFiberData eta g m a r).initialValue,
      (carryMaterialProjectiveFiberData eta g m a r).initialSlope) =
      (baseTwoPhysicalTfvdChannel eta m a r g).2 := by
  change ((eta ^ 0)⁻¹ * _, (eta ^ 1)⁻¹ * _ - (eta ^ 0)⁻¹ * _) = _
  rw [baseTwoPhysicalTfvdChannel_apply]
  change _ = carryWeightedVerticalTrace eta
    (c2BranchVerticalCoordinate m a r (baseTwoPhysicalEdgeC2State g))
  rw [carryWeightedVerticalTrace_apply]
  simp only [pow_zero, inv_one, one_mul, pow_one]
  rfl

/-- This is the weighted TFVD bracket, with its actual one-coordinate shift. -/
theorem carryMaterialProjective_bracket (eta : ℝ) (heta : eta ≠ 0)
    (g : MaterialEdgeL2) (m : PositiveOddCore) (a : C2BranchDirection)
    (r : Fin 2) (j : ℕ) :
    (baseTwoPhysicalTfvdChannel eta m a r g).1 (j + 1) =
      eta ^ (j + 1) * bracket (carryMaterialProjectiveProfile eta g m a r) j := by
  change carryWeightedVerticalCenteredBracket eta
    (c2BranchVerticalCoordinate m a r (baseTwoPhysicalEdgeC2State g)) (j + 1) = _
  rw [carryWeightedVerticalCenteredBracket_succ]
  simp only [c2BranchVerticalCoordinate_apply, bracket, nsmul_eq_mul,
    carryMaterialProjectiveProfile, pow_succ]
  field_simp
  ring

theorem carryMaterialProjective_reconstruct (eta : ℝ) (heta : eta ≠ 0)
    (g : MaterialEdgeL2) (m : PositiveOddCore) (a : C2BranchDirection)
    (r : Fin 2) (j : ℕ) :
    eta ^ j * reconstruct (carryMaterialProjectiveFiberData eta g m a r) j =
      baseTwoPhysicalEdgeC2State g (m, (a, j)) r := by
  rw [carryMaterialProjectiveFiberData, reconstruct_encode]
  exact carryMaterialProjective_regauge eta heta g m a r j

def carryMaterialProjectiveGreenProfile (eta : ℝ) (g : MaterialEdgeL2)
    (m : PositiveOddCore) (a : C2BranchDirection) (r : Fin 2) (j : ℕ) : ℝ :=
  (eta ^ j)⁻¹ * carryMaterialTfvdGreenReadout eta (m, (a, j)) r g

def carryMaterialProjectiveReturnProfile (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (g : MaterialEdgeL2) (m : PositiveOddCore) (a : C2BranchDirection)
    (r : Fin 2) (j : ℕ) : ℝ :=
  (eta ^ j)⁻¹ * carryMaterialTfvdReturnReadout eta h0 h1 (m, (a, j)) r g

theorem carryMaterialProjective_profile_split (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (g : MaterialEdgeL2) (m : PositiveOddCore) (a : C2BranchDirection) (r : Fin 2) :
    carryMaterialProjectiveProfile eta g m a r =
      carryMaterialProjectiveGreenProfile eta g m a r +
        carryMaterialProjectiveReturnProfile eta h0 h1 g m a r := by
  funext j
  simp only [carryMaterialProjectiveProfile, carryMaterialProjectiveGreenProfile,
    carryMaterialProjectiveReturnProfile, Pi.add_apply, ← mul_add]
  rw [carryMaterialTfvd_coordinate]

/-- Scalar differentiability is transported at each fixed physical address.
The existing material connection remains inside the clocked gradient. -/
theorem carryMaterialProjective_profile_hasDerivAt (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (m : PositiveOddCore) (a : C2BranchDirection) (r : Fin 2) (j : ℕ) (t : ℝ) :
    HasDerivAt (fun u => carryMaterialProjectiveProfile eta
      (baseTwoCompletedMaterialGradientL2 u) m a r j)
      ((eta ^ j)⁻¹ * baseTwoPhysicalEdgeC2State
        (-Complex.I • baseTwoCompletedMaterialClockL2 t) (m, (a, j)) r) t := by
  have h := ((carryMaterialTfvdGreen_hasDerivAt eta t (m, (a, j)) r).add
    (carryMaterialTfvdReturn_hasDerivAt eta h0 h1 t (m, (a, j)) r)).const_mul ((eta ^ j)⁻¹)
  simpa only [Pi.add_apply, carryMaterialTfvd_coordinate, carryMaterialProjectiveProfile] using h

theorem carryMaterialProjective_return_affine (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (g : MaterialEdgeL2) (m : PositiveOddCore) (a : C2BranchDirection)
    (r : Fin 2) (j : ℕ) :
    carryMaterialProjectiveReturnProfile eta h0 h1 g m a r j =
      baseTwoPhysicalEdgeC2State g (m, (a, 0)) r +
        (j : ℝ) * (eta⁻¹ * baseTwoPhysicalEdgeC2State g (m, (a, 1)) r -
          baseTwoPhysicalEdgeC2State g (m, (a, 0)) r) := by
  rw [carryMaterialProjectiveReturnProfile, carryMaterialTfvd_return_formula]
  have hn : eta ^ j ≠ 0 := pow_ne_zero j h0.ne'
  exact inv_mul_cancel_left₀ hn _

theorem carryMaterialProjective_return_bracket (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (g : MaterialEdgeL2) (m : PositiveOddCore) (a : C2BranchDirection)
    (r : Fin 2) :
    bracket (carryMaterialProjectiveReturnProfile eta h0 h1 g m a r) = 0 := by
  funext j
  simp only [bracket, carryMaterialProjective_return_affine, Pi.zero_apply,
    nsmul_eq_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
  ring

/-- The valve alone does not observe the actual trace-return. -/
theorem carryMaterialProjective_return_mass (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (g : MaterialEdgeL2) (m : PositiveOddCore) (a : C2BranchDirection) (r : Fin 2) :
    stateMass (carryMaterialProjectiveReturnProfile eta h0 h1 g m a r) = 1 := by
  unfold stateMass
  rw [carryMaterialProjective_return_bracket]
  have hz : ProjectiveDepth.toProjective (PowerSeries.mk (0 : ℕ → ℝ)) = 0 := by
    have hmk : PowerSeries.mk (0 : ℕ → ℝ) = 0 := by ext n; simp
    rw [hmk]
    unfold ProjectiveDepth.toProjective
    rw [← PowerSeries.coe_substAlgHom ProjectiveDepth.inverseCoordinate_hasSubst, map_zero]
  rw [hz, projectiveValveMass_zero]

/-- The full fiber and its Green-only part have the same valve mass.
The boundary coordinates, which generally differ, must still be stored. -/
theorem carryMaterialProjective_mass_eq_green (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (g : MaterialEdgeL2) (m : PositiveOddCore) (a : C2BranchDirection) (r : Fin 2) :
    (carryMaterialProjectiveFiberData eta g m a r).projectiveMass.1 =
      stateMass (carryMaterialProjectiveGreenProfile eta g m a r) := by
  apply (stateMass_eq_iff_bracket_eq _ _).2
  rw [carryMaterialProjective_profile_split eta h0 h1]
  funext j
  have hz := congrFun (carryMaterialProjective_return_bracket eta h0 h1 g m a r) j
  simp only [bracket, Pi.add_apply, Pi.zero_apply, nsmul_eq_mul] at hz ⊢
  linear_combination hz

/-- No Hilbert structure is imposed on these nonlinear coordinates. -/
structure CarryMaterialProjectiveLedger where
  seed : ℂ
  fibers : PositiveOddCore → C2BranchDirection → Fin 2 → ReconstructionData ℝ
  residual : MaterialEdgeL2
  globalReturn : ℂ

def carryMaterialProjectiveEncode (eta : ℝ)
    (y : BaseTwoCompletedBoundaryHilbertCarrier) : CarryMaterialProjectiveLedger where
  seed := y.fst
  fibers := carryMaterialProjectiveFiberData eta y.snd.fst
  residual := baseTwoResidualEdgeProjection y.snd.fst
  globalReturn := y.snd.snd

def carryMaterialProjectiveCoordinate (eta : ℝ) (data : CarryMaterialProjectiveLedger)
    (i : GlobalC2BranchAddress) (r : Fin 2) : ℝ :=
  eta ^ i.2.2 * reconstruct (data.fibers i.1 i.2.1 r) i.2.2

theorem carryMaterialProjective_coordinate_encode (eta : ℝ) (heta : eta ≠ 0)
    (y : BaseTwoCompletedBoundaryHilbertCarrier) (i : GlobalC2BranchAddress) (r : Fin 2) :
    carryMaterialProjectiveCoordinate eta (carryMaterialProjectiveEncode eta y) i r =
      baseTwoPhysicalEdgeC2State y.snd.fst i r :=
  carryMaterialProjective_reconstruct eta heta y.snd.fst i.1 i.2.1 r i.2.2

/-- Faithfulness uses every physical address, the residual, seed and global return. -/
theorem carryMaterialProjectiveEncode_injective (eta : ℝ) (heta : eta ≠ 0) :
    Function.Injective (carryMaterialProjectiveEncode eta) := by
  intro y z he
  have hp : baseTwoPhysicalEdgeC2State y.snd.fst = baseTwoPhysicalEdgeC2State z.snd.fst := by
    ext i r
    rw [← carryMaterialProjective_coordinate_encode eta heta y i r,
      ← carryMaterialProjective_coordinate_encode eta heta z i r, he]
  have hr := congrArg CarryMaterialProjectiveLedger.residual he
  have hg := baseTwoPhysicalResidualC2_injective (Prod.ext hp hr)
  have hs := congrArg CarryMaterialProjectiveLedger.seed he
  have hb := congrArg CarryMaterialProjectiveLedger.globalReturn he
  exact congrArg (WithLp.toLp 2)
    (Prod.ext hs (congrArg (WithLp.toLp 2) (Prod.ext hg hb)))

/-- Independent coordinates and quadratures retain all four TFVD crossings. -/
theorem carryMaterialProjective_crossings (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (y z : BaseTwoCompletedBoundaryHilbertCarrier)
    (i j : GlobalC2BranchAddress) (r s : Fin 2) :
    carryMaterialProjectiveCoordinate eta (carryMaterialProjectiveEncode eta y) i r *
        carryMaterialProjectiveCoordinate eta (carryMaterialProjectiveEncode eta z) j s =
      carryMaterialTfvdGreenReadout eta i r y.snd.fst * carryMaterialTfvdGreenReadout eta j s z.snd.fst +
      carryMaterialTfvdGreenReadout eta i r y.snd.fst * carryMaterialTfvdReturnReadout eta h0 h1 j s z.snd.fst +
      carryMaterialTfvdReturnReadout eta h0 h1 i r y.snd.fst * carryMaterialTfvdGreenReadout eta j s z.snd.fst +
      carryMaterialTfvdReturnReadout eta h0 h1 i r y.snd.fst *
        carryMaterialTfvdReturnReadout eta h0 h1 j s z.snd.fst := by
  rw [carryMaterialProjective_coordinate_encode eta h0.ne',
    carryMaterialProjective_coordinate_encode eta h0.ne',
    ← carryMaterialTfvd_coordinate eta h0 h1 i r y.snd.fst,
    ← carryMaterialTfvd_coordinate eta h0 h1 j s z.snd.fst]
  ring

/-- The original real pairing, evaluated through the faithful nonlinear encoding.
There is no new metric on the ledger and no isometry claim for the valve mass. -/
theorem carryMaterialProjective_full_pairing (eta : ℝ) (heta : eta ≠ 0)
    (y z : BaseTwoCompletedBoundaryHilbertCarrier) :
    inner ℝ y z =
      inner ℝ (carryMaterialProjectiveEncode eta y).seed (carryMaterialProjectiveEncode eta z).seed +
      (∑' i : GlobalC2BranchAddress, ∑ r : Fin 2,
        carryMaterialProjectiveCoordinate eta (carryMaterialProjectiveEncode eta y) i r *
          carryMaterialProjectiveCoordinate eta (carryMaterialProjectiveEncode eta z) i r) +
      inner ℝ (carryMaterialProjectiveEncode eta y).residual
        (carryMaterialProjectiveEncode eta z).residual +
      inner ℝ (carryMaterialProjectiveEncode eta y).globalReturn
        (carryMaterialProjectiveEncode eta z).globalReturn := by
  simp only [carryMaterialProjective_coordinate_encode eta heta]
  have hp : inner ℝ (baseTwoPhysicalEdgeC2State y.snd.fst)
      (baseTwoPhysicalEdgeC2State z.snd.fst) =
      ∑' i : GlobalC2BranchAddress, ∑ r : Fin 2,
        baseTwoPhysicalEdgeC2State y.snd.fst i r * baseTwoPhysicalEdgeC2State z.snd.fst i r := by
    rw [lp.inner_eq_tsum]
    congr 1
    funext i
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro r _
    change (baseTwoPhysicalEdgeC2State z.snd.fst i r) *
      (baseTwoPhysicalEdgeC2State y.snd.fst i r) = _
    ring
  change inner ℝ y.fst z.fst + (inner ℝ y.snd.fst z.snd.fst + inner ℝ y.snd.snd z.snd.snd) = _
  rw [carryMaterial_physical_residual_pairing, hp]
  simp only [carryMaterialProjectiveEncode]
  ring

/-- Both times remain independent; no temporal jets or global strong derivatives
are introduced by this pointwise reconstruction. -/
theorem carryMaterialProjective_source_pairing (eta : ℝ) (heta : eta ≠ 0) (t u : ℝ) :
    inner ℝ (baseTwoCompletedBoundaryHilbertState t) (baseTwoCompletedBoundaryHilbertState u) =
      inner ℝ (criticalMaterialSample t 1) (criticalMaterialSample u 1) +
      (∑' i : GlobalC2BranchAddress, ∑ r : Fin 2,
        carryMaterialProjectiveCoordinate eta
          (carryMaterialProjectiveEncode eta (baseTwoCompletedBoundaryHilbertState t)) i r *
        carryMaterialProjectiveCoordinate eta
          (carryMaterialProjectiveEncode eta (baseTwoCompletedBoundaryHilbertState u)) i r) +
      inner ℝ (baseTwoResidualEdgeProjection (baseTwoCompletedMaterialGradientL2 t))
        (baseTwoResidualEdgeProjection (baseTwoCompletedMaterialGradientL2 u)) +
      inner ℝ (baseTwoCompletedBoundaryValue t) (baseTwoCompletedBoundaryValue u) :=
  carryMaterialProjective_full_pairing eta heta _ _

/-- A nonzero return of the ACTUAL source has unit valve mass. Thus the mass
coordinate cannot replace the boundary coordinates, even on this source. -/
theorem carryMaterialProjective_source_return_invisible (eta : ℝ)
    (h0 : 0 < eta) (h1 : eta < 1) :
    stateMass (carryMaterialProjectiveReturnProfile eta h0 h1
      (baseTwoCompletedMaterialGradientL2 0) c2UnitOddCore 0 0) = 1 ∧
    carryMaterialProjectiveReturnProfile eta h0 h1
      (baseTwoCompletedMaterialGradientL2 0) c2UnitOddCore 0 0 0 < 0 := by
  refine ⟨carryMaterialProjective_return_mass eta h0 h1 _ _ _ _, ?_⟩
  simpa only [carryMaterialProjectiveReturnProfile, pow_zero, inv_one, one_mul] using
    carryMaterialTfvd_return_zero_negative eta h0 h1

/-- The three depths of this actual C2 fiber are material edges 2,6,14.
No depth index is treated as a material index. -/
theorem carryMaterialProjective_unit_curvature (eta t : ℝ) :
    PowerSeries.constantCoeff (carryMaterialProjectiveCurvature eta
      (baseTwoCompletedMaterialGradientL2 t) c2UnitOddCore 0 0) =
      (eta ^ 2)⁻¹ * (criticalMaterialGradient t 14).re -
        2 * (eta⁻¹ * (criticalMaterialGradient t 6).re) +
          (criticalMaterialGradient t 2).re := by
  have ha : baseTwoPhysicalEdgeC2Address (0, 0) = (c2UnitOddCore, (0, 0)) := by
    apply globalC2MaterialAddress_injective
    rw [baseTwoPhysicalEdgeC2Address_material]
    rfl
  have hb : baseTwoPhysicalEdgeC2Address (1, 0) = (c2UnitOddCore, (0, 1)) := by
    apply globalC2MaterialAddress_injective
    rw [baseTwoPhysicalEdgeC2Address_material]
    rfl
  have hc : baseTwoPhysicalEdgeC2Address (3, 0) = (c2UnitOddCore, (0, 2)) := by
    apply globalC2MaterialAddress_injective
    rw [baseTwoPhysicalEdgeC2Address_material]
    rfl
  rw [carryMaterialProjective_curvature_zero, ← ha, ← hb, ← hc,
    baseTwoPhysicalEdgeC2State_apply_edge, baseTwoPhysicalEdgeC2State_apply_edge,
    baseTwoPhysicalEdgeC2State_apply_edge]
  rfl

/-- Exact first curvature of the real, unit-core physical fiber, using the
EXISTING critical ratio. This is a depth coefficient, not a Hilbert energy. -/
theorem carryMaterialProjective_unit_origin_curvature :
    PowerSeries.constantCoeff (carryMaterialProjectiveCurvature
      (criticalVerticalAmplitudeRatio 2 (by decide))
      (baseTwoCompletedMaterialGradientL2 0) c2UnitOddCore 0 0) =
      2 * Real.sqrt 2 / Real.sqrt 7 - 2 / Real.sqrt 15 - 1 / Real.sqrt 3 := by
  have he : criticalVerticalAmplitudeRatio 2 (by decide) = (Real.sqrt 2)⁻¹ :=
    carryMaterial_amplitude_depth_one 2 (by decide)
  have hs8 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    rw [show (8 : ℝ) = 4 * 2 by norm_num, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  have hg14 : (criticalMaterialGradient 0 14).re = (1/4 : ℝ) - (Real.sqrt 15)⁻¹ := by
    norm_num [criticalMaterialGradient, criticalMaterialSample]
    exact Real.sqrt_div_self
  have hg6 : (criticalMaterialGradient 0 6).re = (2 * Real.sqrt 2)⁻¹ - (Real.sqrt 7)⁻¹ := by
    norm_num [criticalMaterialGradient, criticalMaterialSample, hs8]
    rw [Real.sqrt_div_self, Real.sqrt_div_self]
  have hg2 : (criticalMaterialGradient 0 2).re = (1/2 : ℝ) - (Real.sqrt 3)⁻¹ := by
    norm_num [criticalMaterialGradient, criticalMaterialSample]
    exact Real.sqrt_div_self
  rw [carryMaterialProjective_unit_curvature, he, hg14, hg6, hg2]
  simp only [inv_pow, inv_inv, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hs2 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hs3 : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hs7 : Real.sqrt 7 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hs15 : Real.sqrt 15 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  field_simp
  ring

theorem carryMaterialProjective_unit_origin_curvature_neg :
    PowerSeries.constantCoeff (carryMaterialProjectiveCurvature
      (criticalVerticalAmplitudeRatio 2 (by decide))
      (baseTwoCompletedMaterialGradientL2 0) c2UnitOddCore 0 0) < 0 := by
  rw [carryMaterialProjective_unit_origin_curvature]
  have hs3 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hs7 : 0 < Real.sqrt 7 := Real.sqrt_pos.2 (by norm_num)
  have hs15 : 0 < Real.sqrt 15 := Real.sqrt_pos.2 (by norm_num)
  have h3 : (4/7 : ℝ) < 1 / Real.sqrt 3 := by
    apply (lt_div_iff₀ hs3).2
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have h15 : (1/2 : ℝ) < 2 / Real.sqrt 15 := by
    apply (lt_div_iff₀ hs15).2
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 15)]
  have h7 : 2 * Real.sqrt 2 / Real.sqrt 7 < (15/14 : ℝ) := by
    apply (div_lt_iff₀ hs7).2
    apply (sq_lt_sq₀ (by positivity) (by positivity)).mp
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 7)]
  linarith

end
end GeometryOfNumbers.Analysis
