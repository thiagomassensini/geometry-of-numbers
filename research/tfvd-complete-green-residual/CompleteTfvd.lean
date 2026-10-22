import ConfluentKernel
import GeometryOfNumbers.Analysis.CarryMaterialTfvdGreenReadout

/-! Lossless coordinates of the ORIGINAL full material carrier. The range
below records compatibility of actual TFVD data. It has no new metric.
Seed, both real quadratures, material residual and whole-cell return survive.
The inverse is only a coordinate inverse; it is never called a whitening. -/
namespace CarryCompleteTfvd
open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.BaseTwoCompletion
open CarryForcingResidual CarryNativePhase CarryMixedGreen CarryCompletedGreenBalance
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

abbrev MaterialTfvdData := ℂ × ((C2RealTfvdChannels × MaterialEdgeL2) × ℂ)

def materialAnalysis (eta : ℝ) : MaterialCarrier →ₗ[ℝ] MaterialTfvdData where
  toFun y := (y.fst, (baseTwoPhysicalResidualTfvdAnalysis eta y.snd.fst, y.snd.snd))
  map_add' x y := by
    change (x.fst+y.fst, (baseTwoPhysicalResidualTfvdAnalysis eta (x.snd.fst+y.snd.fst),
      x.snd.snd+y.snd.snd)) = _
    rw [map_add]
    rfl
  map_smul' a y := by
    change (a • y.fst, (baseTwoPhysicalResidualTfvdAnalysis eta (a • y.snd.fst),
      a • y.snd.snd)) = _
    rw [map_smul]
    rfl

theorem materialAnalysis_injective (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    Function.Injective (materialAnalysis eta) := by
  intro x y h
  have hs := congrArg (fun z : MaterialTfvdData => z.1) h
  have hg := congrArg (fun z : MaterialTfvdData => z.2.1) h
  have hb := congrArg (fun z : MaterialTfvdData => z.2.2) h
  have he := baseTwoPhysicalResidualTfvdAnalysis_injective eta h0 h1 hg
  change x.fst = y.fst at hs
  change x.snd.snd = y.snd.snd at hb
  apply WithLp.ofLp_injective 2
  apply Prod.ext hs
  apply WithLp.ofLp_injective 2
  exact Prod.ext he hb

/-- Only compatible data are decoded; no arbitrary tuple is declared physical. -/
def materialCoordinates (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    MaterialCarrier ≃ₗ[ℝ] LinearMap.range (materialAnalysis eta) :=
  LinearEquiv.ofInjective (materialAnalysis eta) (materialAnalysis_injective eta h0 h1)

def materialEncode (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :=
  materialCoordinates eta h0 h1

def materialDecode (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :=
  (materialCoordinates eta h0 h1).symm

theorem material_roundtrip (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (y : MaterialCarrier) :
    materialDecode eta h0 h1 (materialEncode eta h0 h1 y) = y :=
  (materialCoordinates eta h0 h1).symm_apply_apply y

theorem material_data_roundtrip (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (z : LinearMap.range (materialAnalysis eta)) :
    materialEncode eta h0 h1 (materialDecode eta h0 h1 z) = z :=
  (materialCoordinates eta h0 h1).apply_symm_apply z

/-- Literal source data: the final scalar is the GLOBAL whole-cell return,
not the separate vertical trace-return inside each fiber. -/
theorem source_data (eta : ℝ) (t : ℝ) :
    materialAnalysis eta (baseTwoCompletedBoundaryHilbertState t) =
      (criticalMaterialSample t 1,
       (baseTwoPhysicalResidualTfvdAnalysis eta (baseTwoCompletedMaterialGradientL2 t),
        baseTwoCompletedBoundaryValue t)) := rfl

/-- Green is evaluated in the original carrier AFTER the complete inverse.
This is an observation, not an inner product on the range. -/
def greenOnData (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (x y : LinearMap.range (materialAnalysis eta) × LinearMap.range (materialAnalysis eta)) : ℂ :=
  carryMaterialPairGreen
    (materialDecode eta h0 h1 x.1, materialDecode eta h0 h1 x.2)
    (materialDecode eta h0 h1 y.1, materialDecode eta h0 h1 y.2)

def pairEncode (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (x : MaterialCarrier × MaterialCarrier) :=
  (materialEncode eta h0 h1 x.1, materialEncode eta h0 h1 x.2)

theorem green_roundtrip (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (x y : MaterialCarrier × MaterialCarrier) :
    greenOnData eta h0 h1 (pairEncode eta h0 h1 x) (pairEncode eta h0 h1 y) =
      carryMaterialPairGreen x y := by
  simp only [greenOnData, pairEncode, material_roundtrip]

theorem original_readout_roundtrip (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (x : MaterialCarrier) :
    baseTwoCompletedBoundaryHilbertReadout (materialDecode eta h0 h1 (materialEncode eta h0 h1 x)) =
      baseTwoCompletedBoundaryHilbertReadout x := by rw [material_roundtrip]

theorem original_pair_reduction_roundtrip (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (t : ℝ) (x : MaterialCarrier × MaterialCarrier) :
    (materialDecode eta h0 h1 (pairEncode eta h0 h1 (carryMaterialPairReduction t x)).1,
      materialDecode eta h0 h1 (pairEncode eta h0 h1 (carryMaterialPairReduction t x)).2) =
      carryMaterialPairReduction t x := by
  simp only [pairEncode, material_roundtrip]

end
end CarryCompleteTfvd
