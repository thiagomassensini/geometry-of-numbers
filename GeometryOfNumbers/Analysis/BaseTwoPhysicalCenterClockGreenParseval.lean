import GeometryOfNumbers.Analysis.BaseTwoPhysicalCenterClockDefect
import GeometryOfNumbers.Analysis.GreenParsevalMaterialLogOperator

/-! # Exact center-clock decomposition through material Green and Parseval
Only the existing address/quadrature isometries package the physical states.
The material generator domain is proved by a finite-energy representative of
the endpoint diagonal term. No amplitude-source identification is involved.
-/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators lp ENNReal
namespace GeometryOfNumbers.Analysis.BaseTwoCompletion
open C2GlobalGreenBridge GreenFrame.Concrete GreenStateMaterialLog GreenParsevalMaterialLog

private theorem centerClockC2_difference (t : ℝ) (e : BaseTwoPhysicalEdge) :
    (baseTwoPhysicalLogGradientC2State t - baseTwoPhysicalCenterClockDefectC2State t)
      (baseTwoPhysicalEdgeC2Address e) =
    baseTwoPhysicalOddEndpointLog e •
      baseTwoPhysicalOrdinaryC2State t (baseTwoPhysicalEdgeC2Address e) := by
  change baseTwoPhysicalLogGradientC2State t (baseTwoPhysicalEdgeC2Address e) -
    baseTwoPhysicalCenterClockDefectC2State t (baseTwoPhysicalEdgeC2Address e) = _
  rw [baseTwoPhysicalLogGradientC2State_apply,
    baseTwoPhysicalCenterClockDefectC2State_apply, baseTwoPhysicalOrdinaryC2State_apply,
    ← map_sub, ← map_smul]
  congr 1
  change baseTwoNativeLogGradientFormula t (baseTwoPhysicalEdgeIndex e) -
    baseTwoPhysicalCenterClockDefect t e =
      (baseTwoPhysicalOddEndpointLog e : ℂ) * criticalMaterialGradient t (baseTwoPhysicalEdgeIndex e)
  unfold baseTwoPhysicalCenterClockDefect baseTwoPhysicalEndpointClock
  ring

/-- Literal diagonal action by the decoded odd material integer. Membership is
certified by the already existing log-gradient minus the finite-energy defect. -/
def baseTwoPhysicalOddEndpointDiagonalClock (t : ℝ) : GlobalC2BranchCarrier :=
  ⟨fun a => Real.log ((globalC2MaterialAddress a : ℕ) : ℝ) •
    baseTwoPhysicalOrdinaryC2State t a, by
    have he : (fun a => Real.log ((globalC2MaterialAddress a : ℕ) : ℝ) •
        baseTwoPhysicalOrdinaryC2State t a) =
        (fun a => (baseTwoPhysicalLogGradientC2State t -
          baseTwoPhysicalCenterClockDefectC2State t) a) := by
      funext a
      obtain ⟨e,rfl⟩ := baseTwoPhysicalEdgeEquivC2Address.surjective a
      change Real.log ((globalC2MaterialAddress (baseTwoPhysicalEdgeC2Address e) : ℕ) : ℝ) •
        baseTwoPhysicalOrdinaryC2State t (baseTwoPhysicalEdgeC2Address e) =
        (baseTwoPhysicalLogGradientC2State t -
          baseTwoPhysicalCenterClockDefectC2State t) (baseTwoPhysicalEdgeC2Address e)
      rw [baseTwoPhysicalEdgeC2Address_material]
      exact (centerClockC2_difference t e).symm
    rw [he]
    exact lp.memℓp _⟩

theorem baseTwoPhysicalOddEndpointDiagonalClock_apply (t : ℝ) (e : BaseTwoPhysicalEdge) :
    baseTwoPhysicalOddEndpointDiagonalClock t (baseTwoPhysicalEdgeC2Address e) =
      baseTwoPhysicalOddEndpointLog e •
        baseTwoPhysicalOrdinaryC2State t (baseTwoPhysicalEdgeC2Address e) := by
  change Real.log ((globalC2MaterialAddress (baseTwoPhysicalEdgeC2Address e) : ℕ) : ℝ) • _ = _
  rw [baseTwoPhysicalEdgeC2Address_material]; rfl

theorem baseTwoPhysicalClock_C2_decomposition (t : ℝ) :
    baseTwoPhysicalLogGradientC2State t =
      baseTwoPhysicalOddEndpointDiagonalClock t + baseTwoPhysicalCenterClockDefectC2State t := by
  apply lp.ext; funext a
  obtain ⟨e,rfl⟩ := baseTwoPhysicalEdgeEquivC2Address.surjective a
  have h := centerClockC2_difference t e
  change baseTwoPhysicalLogGradientC2State t (baseTwoPhysicalEdgeC2Address e) -
    baseTwoPhysicalCenterClockDefectC2State t (baseTwoPhysicalEdgeC2Address e) =
    baseTwoPhysicalOddEndpointLog e •
      baseTwoPhysicalOrdinaryC2State t (baseTwoPhysicalEdgeC2Address e) at h
  change baseTwoPhysicalLogGradientC2State t (baseTwoPhysicalEdgeC2Address e) =
    baseTwoPhysicalOddEndpointDiagonalClock t (baseTwoPhysicalEdgeC2Address e) +
    baseTwoPhysicalCenterClockDefectC2State t (baseTwoPhysicalEdgeC2Address e)
  rw [baseTwoPhysicalOddEndpointDiagonalClock_apply]
  exact sub_eq_iff_eq_add.mp h

/-- Existing index and real-quadrature packaging, composed without amplitudes. -/
def baseTwoPhysicalC2GreenIsometry : GlobalC2BranchCarrier →ₗᵢ[ℝ] State :=
  oddMaterialToGreenState.comp globalBranchIncidenceIsometry.toLinearIsometry

theorem baseTwoPhysicalC2GreenIsometry_apply (x : GlobalC2BranchCarrier)
    (e : BaseTwoPhysicalEdge) :
    baseTwoPhysicalC2GreenIsometry x (baseTwoPhysicalEdgeOddEndpoint e).val =
      realPlaneToComplexIsometry (x (baseTwoPhysicalEdgeC2Address e)) := by
  change oddMaterialToGreenState (globalBranchIncidenceIsometry x) _ = _
  rw [oddMaterialToGreenState_apply]
  rfl

theorem baseTwoPhysicalC2GreenIsometry_off_sector (x : GlobalC2BranchCarrier) (n : PNat)
    (hn : ¬ (Odd (n : ℕ) ∧ 3 ≤ (n : ℕ))) : baseTwoPhysicalC2GreenIsometry x n = 0 :=
  oddMaterialToGreenState_apply_off_sector _ n hn

theorem baseTwoPhysicalC2GreenIsometry_norm (x : GlobalC2BranchCarrier) :
    ‖baseTwoPhysicalC2GreenIsometry x‖ = ‖x‖ :=
  baseTwoPhysicalC2GreenIsometry.norm_map x

def baseTwoPhysicalOrdinaryGreenState (t : ℝ) : State :=
  baseTwoPhysicalC2GreenIsometry (baseTwoPhysicalOrdinaryC2State t)

def baseTwoPhysicalLogGradientGreenState (t : ℝ) : State :=
  baseTwoPhysicalC2GreenIsometry (baseTwoPhysicalLogGradientC2State t)

def baseTwoPhysicalCenterClockDefectGreenState (t : ℝ) : State :=
  baseTwoPhysicalC2GreenIsometry (baseTwoPhysicalCenterClockDefectC2State t)

def baseTwoPhysicalOddEndpointClockGreenState (t : ℝ) : State :=
  baseTwoPhysicalC2GreenIsometry (baseTwoPhysicalOddEndpointDiagonalClock t)

theorem baseTwoPhysicalOrdinaryGreenState_apply (t : ℝ) (e : BaseTwoPhysicalEdge) :
    baseTwoPhysicalOrdinaryGreenState t (baseTwoPhysicalEdgeOddEndpoint e).val =
      criticalMaterialGradient t (baseTwoPhysicalEdgeIndex e) := by
  rw [baseTwoPhysicalOrdinaryGreenState, baseTwoPhysicalC2GreenIsometry_apply,
    baseTwoPhysicalOrdinaryC2State_apply, baseTwoMaterialEdgeRealification_pack]

theorem baseTwoPhysicalLogGradientGreenState_apply (t : ℝ) (e : BaseTwoPhysicalEdge) :
    baseTwoPhysicalLogGradientGreenState t (baseTwoPhysicalEdgeOddEndpoint e).val =
      baseTwoNativeLogGradientFormula t (baseTwoPhysicalEdgeIndex e) := by
  rw [baseTwoPhysicalLogGradientGreenState, baseTwoPhysicalC2GreenIsometry_apply,
    baseTwoPhysicalLogGradientC2State_apply, baseTwoMaterialEdgeRealification_pack]

theorem baseTwoPhysicalCenterClockDefectGreenState_apply (t : ℝ) (e : BaseTwoPhysicalEdge) :
    baseTwoPhysicalCenterClockDefectGreenState t (baseTwoPhysicalEdgeOddEndpoint e).val =
      baseTwoPhysicalCenterClockDefect t e := by
  rw [baseTwoPhysicalCenterClockDefectGreenState, baseTwoPhysicalC2GreenIsometry_apply,
    baseTwoPhysicalCenterClockDefectC2State_apply, baseTwoMaterialEdgeRealification_pack]

private theorem endpointGreen_apply_edge (t : ℝ) (e : BaseTwoPhysicalEdge) :
    baseTwoPhysicalOddEndpointClockGreenState t (baseTwoPhysicalEdgeOddEndpoint e).val =
      (baseTwoPhysicalOddEndpointLog e : ℂ) *
        baseTwoPhysicalOrdinaryGreenState t (baseTwoPhysicalEdgeOddEndpoint e).val := by
  rw [baseTwoPhysicalOddEndpointClockGreenState, baseTwoPhysicalC2GreenIsometry_apply,
    baseTwoPhysicalOddEndpointDiagonalClock_apply, map_smul]
  change _ = (baseTwoPhysicalOddEndpointLog e : ℂ) * _
  rw [baseTwoPhysicalOrdinaryGreenState, baseTwoPhysicalC2GreenIsometry_apply]
  rfl

/-- The completed endpoint clock is literally log(n) multiplication on State. -/
theorem baseTwoPhysicalOddEndpointClockGreenState_apply (t : ℝ) (n : PNat) :
    baseTwoPhysicalOddEndpointClockGreenState t n =
      (Real.log (n : ℝ) : ℂ) * baseTwoPhysicalOrdinaryGreenState t n := by
  by_cases hn : Odd (n : ℕ) ∧ 3 ≤ (n : ℕ)
  · let q : OddMaterialIndex := ⟨n,hn⟩
    obtain ⟨e,he⟩ := baseTwoPhysicalEdgeEquivOddMaterial.surjective q
    have hv : (baseTwoPhysicalEdgeOddEndpoint e).val = n := congrArg Subtype.val he
    have h := endpointGreen_apply_edge t e
    unfold baseTwoPhysicalOddEndpointLog at h
    simpa only [hv] using h
  · rw [baseTwoPhysicalOddEndpointClockGreenState, baseTwoPhysicalOrdinaryGreenState,
      baseTwoPhysicalC2GreenIsometry_off_sector _ n hn,
      baseTwoPhysicalC2GreenIsometry_off_sector _ n hn, mul_zero]

theorem baseTwoPhysicalClock_Green_decomposition (t : ℝ) :
    baseTwoPhysicalLogGradientGreenState t =
      baseTwoPhysicalOddEndpointClockGreenState t + baseTwoPhysicalCenterClockDefectGreenState t := by
  unfold baseTwoPhysicalLogGradientGreenState baseTwoPhysicalOddEndpointClockGreenState
    baseTwoPhysicalCenterClockDefectGreenState
  rw [baseTwoPhysicalClock_C2_decomposition, map_add]

/-- No domain assumption: the diagonal has an actual L2 representative. -/
theorem baseTwoPhysicalOrdinaryGreenState_mem_domain (t : ℝ) :
    baseTwoPhysicalOrdinaryGreenState t ∈ greenStateMaterialLogGenerator.domain := by
  rw [greenStateMaterialLogGenerator_domain_iff_memℓp]
  have he : (fun n : PNat => (Real.log (n : ℝ) : ℂ) * baseTwoPhysicalOrdinaryGreenState t n) =
      (fun n => baseTwoPhysicalOddEndpointClockGreenState t n) :=
    funext (fun n => (baseTwoPhysicalOddEndpointClockGreenState_apply t n).symm)
  rw [he]
  exact lp.memℓp _

theorem baseTwoPhysicalMaterialLogGenerator_eq_endpoint (t : ℝ) :
    greenStateMaterialLogGenerator
      ⟨baseTwoPhysicalOrdinaryGreenState t,baseTwoPhysicalOrdinaryGreenState_mem_domain t⟩ =
    baseTwoPhysicalOddEndpointClockGreenState t := by
  apply lp.ext; funext n
  rw [greenStateMaterialLogGenerator_apply, baseTwoPhysicalOddEndpointClockGreenState_apply]

/-- True transported log-gradient = the self-adjoint material clock + center coupling. -/
theorem baseTwoPhysicalClock_Green_generator_decomposition (t : ℝ) :
    baseTwoPhysicalLogGradientGreenState t =
      greenStateMaterialLogGenerator
        ⟨baseTwoPhysicalOrdinaryGreenState t,baseTwoPhysicalOrdinaryGreenState_mem_domain t⟩ +
      baseTwoPhysicalCenterClockDefectGreenState t := by
  rw [baseTwoPhysicalMaterialLogGenerator_eq_endpoint, baseTwoPhysicalClock_Green_decomposition]

def baseTwoPhysicalOrdinaryParsevalState (t : ℝ) : ConcreteAnalysisSpace :=
  greenParsevalAnalysis (baseTwoPhysicalOrdinaryGreenState t)

def baseTwoPhysicalLogGradientParsevalState (t : ℝ) : ConcreteAnalysisSpace :=
  greenParsevalAnalysis (baseTwoPhysicalLogGradientGreenState t)

def baseTwoPhysicalCenterClockDefectParsevalState (t : ℝ) : ConcreteAnalysisSpace :=
  greenParsevalAnalysis (baseTwoPhysicalCenterClockDefectGreenState t)

theorem baseTwoPhysicalOrdinaryParsevalState_mem_domain (t : ℝ) :
    baseTwoPhysicalOrdinaryParsevalState t ∈ greenParsevalMaterialLogOperator.domain :=
  (greenParsevalMaterialLogOperator_P_mem_domain_iff _).mpr
    (baseTwoPhysicalOrdinaryGreenState_mem_domain t)

/-- Exact transport by the existing canonical Parseval analysis and operator. -/
theorem baseTwoPhysicalClock_Parseval_decomposition (t : ℝ) :
    baseTwoPhysicalLogGradientParsevalState t =
      greenParsevalMaterialLogOperator
        ⟨baseTwoPhysicalOrdinaryParsevalState t,baseTwoPhysicalOrdinaryParsevalState_mem_domain t⟩ +
      baseTwoPhysicalCenterClockDefectParsevalState t := by
  unfold baseTwoPhysicalLogGradientParsevalState baseTwoPhysicalCenterClockDefectParsevalState
  rw [baseTwoPhysicalClock_Green_generator_decomposition, map_add]
  congr 1
  exact (greenParsevalMaterialLogOperator_intertwining _
    (baseTwoPhysicalOrdinaryGreenState_mem_domain t)).symm

/-- Finite reconstruction retains seed, physical and residual material information. -/
theorem baseTwoCenterSample_eq_seed_physical_residual_prefix (t : ℝ) (k : ℕ) :
    criticalMaterialSample t (baseTwoCenter k) = criticalMaterialSample t 1 +
      (∑ j ∈ Finset.range (baseTwoCenter k - 1),
        baseTwoPhysicalEdgeProjection (baseTwoCompletedMaterialGradientL2 t) j) +
      (∑ j ∈ Finset.range (baseTwoCenter k - 1),
        baseTwoResidualEdgeProjection (baseTwoCompletedMaterialGradientL2 t) j) := by
  have hc : baseTwoCenter k-1+1 = baseTwoCenter k := by simp [baseTwo_center_eq]; omega
  rw [← hc, criticalMaterialSample_eq_seed_add_gradientPrefix]
  rw [hc]
  have he : (fun j => criticalMaterialGradient t j) =
      (fun j => baseTwoPhysicalEdgeProjection (baseTwoCompletedMaterialGradientL2 t) j +
        baseTwoResidualEdgeProjection (baseTwoCompletedMaterialGradientL2 t) j) := by
    funext j
    have h := congrArg (fun g : MaterialEdgeL2 => g j)
      (baseTwoPhysicalResidual_reconstruction (baseTwoCompletedMaterialGradientL2 t))
    exact h.symm
  rw [he, Finset.sum_add_distrib]
  abel

end GeometryOfNumbers.Analysis.BaseTwoCompletion
