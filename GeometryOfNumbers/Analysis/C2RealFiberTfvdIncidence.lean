import GeometryOfNumbers.Analysis.C2GlobalPhysicalBranchCanary
import GeometryOfNumbers.Analysis.RealCarryTfvd
import GeometryOfNumbers.Analysis.PolarizedMomentCoefficients

/-!
# Provenance-preserving real TFVD analysis of C2 address fibers

Core, direction and quadrature remain external labels. The vertical coordinate
j is the existing depth-from-two chart: physical depth is j + 2. No material
integer is used as a vertical index. These are incidence vectors, not completed
moment jets. Their independence alone is not a moment readout theorem.
-/
namespace GeometryOfNumbers.Analysis
noncomputable section
open RealCarry
open scoped lp ENNReal

/-- The already existing vertical Hilbert space in each C2 fiber/quadrature. -/
abbrev C2RealVerticalChannels :=
  PositiveOddCore → C2BranchDirection → Fin 2 → CarryVerticalL2

/-- TFVD keeps both the interior and the two boundary data in every channel. -/
abbrev C2RealTfvdChannels :=
  PositiveOddCore → C2BranchDirection → Fin 2 → (CarryVerticalL2 × (ℝ × ℝ))

private theorem fiber_mem (x : GlobalC2BranchCarrier) (m : PositiveOddCore)
    (a : C2BranchDirection) (r : Fin 2) :
    Memℓp (fun j : ℕ => x (m, (a, j)) r) 2 := by
  have hs := (lp.memℓp x).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  have hi : Function.Injective (fun j : ℕ => (m, (a, j))) := by
    intro j k h
    exact congrArg (fun i : GlobalC2BranchAddress => i.2.2) h
  have hf : Memℓp (fun j : ℕ => x (m, (a, j))) 2 := by
    rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    exact hs.comp_injective hi
  exact hf.mono' (fun j => PiLp.norm_apply_le (x (m, (a, j))) r)

/-- Exact extraction of a real quadrature along a fixed core/direction fiber. -/
def c2BranchVerticalCoordinate (m : PositiveOddCore) (a : C2BranchDirection)
    (r : Fin 2) : GlobalC2BranchCarrier →ₗ[ℝ] CarryVerticalL2 where
  toFun x := ⟨fun j => x (m, (a, j)) r, fiber_mem x m a r⟩
  map_add' x y := by ext j; rfl
  map_smul' c x := by ext j; rfl

theorem c2BranchVerticalCoordinate_apply (m : PositiveOddCore)
    (a : C2BranchDirection) (r : Fin 2) (x : GlobalC2BranchCarrier) (j : ℕ) :
    c2BranchVerticalCoordinate m a r x j = x (m, (a, j)) r := rfl

/-- Retain every core, sign, vertical coordinate and both real quadratures. -/
def c2BranchVerticalCoordinates : GlobalC2BranchCarrier →ₗ[ℝ] C2RealVerticalChannels where
  toFun x m a r := c2BranchVerticalCoordinate m a r x
  map_add' x y := by ext m a r j; rfl
  map_smul' c x := by ext m a r j; rfl

theorem c2BranchVerticalCoordinates_injective :
    Function.Injective c2BranchVerticalCoordinates := by
  intro x y h
  ext i r
  exact congrArg (fun z : C2RealVerticalChannels => z i.1 i.2.1 r i.2.2) h

/-- The R2 analysis acts only inside each actual vertical fiber. -/
def c2FiberTfvdAnalysis (eta : ℝ) : GlobalC2BranchCarrier →ₗ[ℝ] C2RealTfvdChannels where
  toFun x m a r := realCarryTfvdAnalysis eta (c2BranchVerticalCoordinate m a r x)
  map_add' x y := by
    funext m a r
    exact ((realCarryTfvdAnalysis eta).toLinearMap.comp
      (c2BranchVerticalCoordinate m a r)).map_add x y
  map_smul' c x := by
    funext m a r
    exact ((realCarryTfvdAnalysis eta).toLinearMap.comp
      (c2BranchVerticalCoordinate m a r)).map_smul c x

/-- Pointwise synthesis, including each fiber's trace/return data. -/
def c2FiberTfvdSynthesis (eta : ℝ) (h0 : 0 ≤ eta) (h1 : eta < 1) :
    C2RealTfvdChannels →ₗ[ℝ] C2RealVerticalChannels where
  toFun x m a r := realCarryTfvdSynthesis eta h0 h1 (x m a r)
  map_add' x y := by
    funext m a r
    exact (realCarryTfvdSynthesis eta h0 h1).map_add (x m a r) (y m a r)
  map_smul' c x := by
    funext m a r
    exact (realCarryTfvdSynthesis eta h0 h1).map_smul c (x m a r)

/-- No reconstruction is reproved: this is the R2 left inverse in every fiber. -/
theorem c2FiberTfvdSynthesis_analysis (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (x : GlobalC2BranchCarrier) :
    c2FiberTfvdSynthesis eta h0.le h1 (c2FiberTfvdAnalysis eta x) =
      c2BranchVerticalCoordinates x := by
  funext m a r
  exact DFunLike.congr_fun (realCarryTfvdSynthesis_comp_analysis eta h0 h1)
    (c2BranchVerticalCoordinate m a r x)

theorem c2FiberTfvdAnalysis_injective (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    Function.Injective (c2FiberTfvdAnalysis eta) := by
  intro x y h
  apply c2BranchVerticalCoordinates_injective
  have hh := congrArg (c2FiberTfvdSynthesis eta h0.le h1) h
  rw [c2FiberTfvdSynthesis_analysis eta h0 h1 x,
    c2FiberTfvdSynthesis_analysis eta h0 h1 y] at hh
  exact hh

/-- Incidence decoding precedes TFVD; the material label is never treated as depth. -/
def c2OddMaterialTfvdAnalysis (eta : ℝ) : OddMaterialState →ₗ[ℝ] C2RealTfvdChannels :=
  (c2FiberTfvdAnalysis eta).comp globalBranchIncidenceIsometry.symm.toLinearEquiv.toLinearMap

theorem c2OddMaterialTfvdAnalysis_injective (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    Function.Injective (c2OddMaterialTfvdAnalysis eta) :=
  (c2FiberTfvdAnalysis_injective eta h0 h1).comp globalBranchIncidenceIsometry.symm.injective

/-- Coordinate readout after canonical material incidence decoding. -/
theorem c2OddMaterial_verticalCoordinate (x : OddMaterialState)
    (m : PositiveOddCore) (a : C2BranchDirection) (r : Fin 2) (j : ℕ) :
    c2BranchVerticalCoordinate m a r (globalBranchIncidenceIsometry.symm x) j =
      x (globalC2OddMaterialAddress (m, (a, j))) r := by
  have h := globalBranchIncidenceIsometry_apply_address
    (globalBranchIncidenceIsometry.symm x) (m, (a, j))
  rw [globalBranchIncidenceIsometry.apply_symm_apply] at h
  exact (congrArg (fun v : RealPlaneHilbert => v r) h).symm

/-- The canonical smallest positive odd core; no choice of a decomposition. -/
def c2UnitOddCore : PositiveOddCore := ⟨1, by decide, by decide⟩

/-- Two physical directions at every depth of the unit-core fiber. -/
def c2ParityIncidenceAddress : (ℕ ⊕ ℕ) → GlobalC2BranchAddress
  | Sum.inl j => (c2UnitOddCore, (0, j))
  | Sum.inr j => (c2UnitOddCore, (1, j))

theorem c2ParityIncidenceAddress_injective : Function.Injective c2ParityIncidenceAddress := by
  intro i j h
  cases i <;> cases j
  · have hh := congrArg (fun x : GlobalC2BranchAddress => x.2.2) h
    congr 1
  · have hh := congrArg (fun x : GlobalC2BranchAddress => x.2.1) h
    norm_num [c2ParityIncidenceAddress] at hh
  · have hh := congrArg (fun x : GlobalC2BranchAddress => x.2.1) h
    norm_num [c2ParityIncidenceAddress] at hh
  · have hh := congrArg (fun x : GlobalC2BranchAddress => x.2.2) h
    congr 1

/-- Center of the same physical address, not a freely selected coordinate. -/
def c2ParityIncidenceCenter (i : ℕ ⊕ ℕ) : ℕ :=
  2 ^ c2BranchDepth (c2ParityIncidenceAddress i).2 * (c2ParityIncidenceAddress i).1.val

def c2ParityIncidenceLeg (i : ℕ ⊕ ℕ) : PNat :=
  globalC2MaterialAddress (c2ParityIncidenceAddress i)

theorem c2ParityIncidence_left (j : ℕ) :
    (c2ParityIncidenceLeg (Sum.inl j) : ℕ) = c2ParityIncidenceCenter (Sum.inl j) - 1 := rfl

theorem c2ParityIncidence_right (j : ℕ) :
    (c2ParityIncidenceLeg (Sum.inr j) : ℕ) = c2ParityIncidenceCenter (Sum.inr j) + 1 := by
  simp [c2ParityIncidenceLeg, globalC2MaterialAddress, c2BranchMaterialAddress,
    c2BranchMaterialNat, c2ParityIncidenceAddress, c2ParityIncidenceCenter]

/-- The encoded material endpoint retains the intrinsic C2 neighbor depth. -/
theorem c2ParityIncidence_depth_recovery (i : ℕ ⊕ ℕ) (r : ℕ) :
    C2LegHasCarryDepthAtLeast (c2ParityIncidenceLeg i) r ↔
      r ≤ c2BranchDepth (c2ParityIncidenceAddress i).2 :=
  c2BranchMaterialAddress_depth_recovery _ (c2ParityIncidenceAddress i).1.property.1
    (c2ParityIncidenceAddress i).1.property.2 _ r

theorem c2ParityIncidence_center_ne_leg (i j : ℕ ⊕ ℕ) :
    c2ParityIncidenceCenter i ≠ (c2ParityIncidenceLeg j : ℕ) := by
  have hl := globalC2MaterialAddress_odd (c2ParityIncidenceAddress j)
  change Odd (c2ParityIncidenceLeg j : ℕ) at hl
  rw [Nat.odd_iff] at hl
  have hc : c2ParityIncidenceCenter i % 2 = 0 := by
    cases i <;> simp [c2ParityIncidenceCenter, c2ParityIncidenceAddress,
      c2UnitOddCore, c2BranchDepth, pow_add, Nat.mul_mod]
  intro h
  rw [← h, hc] at hl
  norm_num at hl

/-- Coordinate incidence seed. It has no moment-dependent coefficient or dressing. -/
def c2RealIncidenceJet (i : ℕ ⊕ ℕ) : GlobalC2BranchCarrier :=
  lp.single 2 (c2ParityIncidenceAddress i) (realPlaneHilbertEquiv (1, 0))

private def firstQuadrature : GlobalC2BranchCarrier →ₗ[ℝ] (GlobalC2BranchAddress → ℝ) where
  toFun x i := x i 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem c2RealIncidenceJet_linearIndependent : LinearIndependent ℝ c2RealIncidenceJet := by
  have hi := (Pi.linearIndependent_single_one GlobalC2BranchAddress ℝ).comp
    c2ParityIncidenceAddress c2ParityIncidenceAddress_injective
  apply LinearIndependent.of_comp firstQuadrature
  convert hi using 1
  funext i a
  by_cases h : a = c2ParityIncidenceAddress i
  · simp [firstQuadrature, c2RealIncidenceJet, lp.single_apply,
      realPlaneHilbertEquiv, h]
  · simp [firstQuadrature, c2RealIncidenceJet, lp.single_apply,
      h]

/-- Exact real fiber analysis of existing incidence vectors, not canonical moment jets. -/
def c2RealTfvdIncidenceJet (eta : ℝ) (i : ℕ ⊕ ℕ) : C2RealTfvdChannels :=
  c2FiberTfvdAnalysis eta (c2RealIncidenceJet i)

theorem c2RealTfvdIncidenceJet_linearIndependent (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    LinearIndependent ℝ (c2RealTfvdIncidenceJet eta) :=
  c2RealIncidenceJet_linearIndependent.map_injOn (c2FiberTfvdAnalysis eta)
    (c2FiberTfvdAnalysis_injective eta h0 h1).injOn

theorem c2RealTfvdIncidenceJet_even_linearIndependent (eta : ℝ)
    (h0 : 0 < eta) (h1 : eta < 1) :
    LinearIndependent ℝ (fun j : ℕ => c2RealTfvdIncidenceJet eta (Sum.inl j)) :=
  (c2RealTfvdIncidenceJet_linearIndependent eta h0 h1).comp Sum.inl Sum.inl_injective

theorem c2RealTfvdIncidenceJet_odd_linearIndependent (eta : ℝ)
    (h0 : 0 < eta) (h1 : eta < 1) :
    LinearIndependent ℝ (fun j : ℕ => c2RealTfvdIncidenceJet eta (Sum.inr j)) :=
  (c2RealTfvdIncidenceJet_linearIndependent eta h0 h1).comp Sum.inr Sum.inr_injective

theorem c2RealTfvdIncidenceJet_even_prefix_linearIndependent (eta : ℝ)
    (h0 : 0 < eta) (h1 : eta < 1) (N : ℕ) :
    LinearIndependent ℝ (fun j : Fin N => c2RealTfvdIncidenceJet eta (Sum.inl j.val)) :=
  (c2RealTfvdIncidenceJet_even_linearIndependent eta h0 h1).comp
    Fin.val Fin.val_injective

theorem c2RealTfvdIncidenceJet_odd_prefix_linearIndependent (eta : ℝ)
    (h0 : 0 < eta) (h1 : eta < 1) (N : ℕ) :
    LinearIndependent ℝ (fun j : Fin N => c2RealTfvdIncidenceJet eta (Sum.inr j.val)) :=
  (c2RealTfvdIncidenceJet_odd_linearIndependent eta h0 h1).comp
    Fin.val Fin.val_injective

/-- Critical base-two specialization uses the ratio already derived upstream. -/
theorem c2CriticalOddMaterialTfvdAnalysis_injective :
    Function.Injective (c2OddMaterialTfvdAnalysis
      (criticalVerticalAmplitudeRatio 2 (by norm_num))) :=
  c2OddMaterialTfvdAnalysis_injective _
    (criticalVerticalAmplitudeRatio_pos 2 _) (criticalVerticalAmplitudeRatio_lt_one 2 (by norm_num))

end
end GeometryOfNumbers.Analysis
