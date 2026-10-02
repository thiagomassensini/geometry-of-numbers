import GeometryOfNumbers.Analysis.RealMultiplicativeValve

/-! # Faithful state encoding by boundary and normalized projective mass

Local rewrite of the historical finite algebra; see SOURCE_PROVENANCE.md.
-/

namespace GeometryOfNumbers.Analysis.DiscreteProjective

open PowerSeries
open DiscreteValve ProjectiveDepth ProjectiveValve

noncomputable section

theorem discreteBracket_eq_causalUnitBracket
    {E : Type*} [AddCommGroup E] (f : ℕ → E) (n : ℕ) :
    bracket f n = causalUnitBracket f n := by
  unfold bracket causalUnitBracket
  abel

@[ext] structure ReconstructionData (K : Type*) [Field K] where
  initialValue : K
  initialSlope : K
  projectiveMass : NormalizedProjectiveMass K

variable {K : Type*} [Field K]

def reconstructionBracketData (data : ReconstructionData K) :
    CausalBracketData K where
  leftSeed := data.initialValue
  centerSeed := data.initialValue + data.initialSlope
  bracket n := coeff n
    (fromProjective (projectiveValveCurvature data.projectiveMass.1))

def reconstruct (data : ReconstructionData K) : ℕ → K :=
  causalBracketReconstruction (reconstructionBracketData data)

@[simp] theorem reconstruct_zero (data : ReconstructionData K) :
    reconstruct data 0 = data.initialValue := rfl

@[simp] theorem reconstruct_fdiff_zero (data : ReconstructionData K) :
    fdiff (reconstruct data) 0 = data.initialSlope := by
  change (data.initialValue + data.initialSlope) - data.initialValue =
    data.initialSlope
  abel

@[simp] theorem bracket_reconstruct (data : ReconstructionData K) (n : ℕ) :
    bracket (reconstruct data) n =
      coeff n (fromProjective (projectiveValveCurvature data.projectiveMass.1)) := by
  rw [discreteBracket_eq_causalUnitBracket]
  exact causalUnitBracket_reconstruction (reconstructionBracketData data) n

theorem mk_bracket_reconstruct (data : ReconstructionData K) :
    mk (bracket (reconstruct data)) =
      fromProjective (projectiveValveCurvature data.projectiveMass.1) := by
  ext n
  rw [coeff_mk, bracket_reconstruct]

theorem mk_reconstruct_eq_green (data : ReconstructionData K) :
    mk (reconstruct data) =
      C data.initialValue * geometricSeries +
        X * C data.initialSlope * greenKernelSeries +
        X ^ 2 * greenKernelSeries *
          fromProjective (projectiveValveCurvature data.projectiveMass.1) := by
  rw [mk_discrete_valve, reconstruct_zero, reconstruct_fdiff_zero,
    mk_bracket_reconstruct]

variable [CharZero K]

/-- State → vertical bracket → projective transport → normalized mass. -/
def stateMass (f : ℕ → K) : PowerSeries K :=
  projectiveValveMass (toProjective (mk (bracket f)))

theorem stateMass_eq_projectiveGreenMass (f : ℕ → K) :
    stateMass f =
      GreenValve.projectiveGreenMass (mk (bracket f)) := by
  exact projectiveValveMass_toProjective (mk (bracket f))

@[simp] theorem stateMass_constantCoeff (f : ℕ → K) :
    constantCoeff (stateMass f) = 1 :=
  projectiveValveMass_constantCoeff (toProjective (mk (bracket f)))

@[simp] theorem projectiveValveCurvature_stateMass (f : ℕ → K) :
    projectiveValveCurvature (stateMass f) =
      toProjective (mk (bracket f)) :=
  projectiveValveCurvature_projectiveValveMass (toProjective (mk (bracket f)))

theorem stateMass_eq_iff_bracket_eq (f g : ℕ → K) :
    stateMass f = stateMass g ↔ bracket f = bracket g := by
  constructor
  · intro hmass
    have hcurvature :
        toProjective (mk (bracket f)) =
          toProjective (mk (bracket g)) :=
      projectiveValveMass_injective hmass
    have hseries : mk (bracket f) = mk (bracket g) := by
      simpa only [fromProjective_toProjective] using
        congrArg (fromProjective (R := K)) hcurvature
    funext n
    simpa only [coeff_mk] using congrArg (coeff n) hseries
  · intro hbracket
    unfold stateMass
    rw [hbracket]

theorem eq_of_boundary_and_stateMass_eq
    {f g : ℕ → K}
    (hvalue : f 0 = g 0)
    (hslope : fdiff f 0 = fdiff g 0)
    (hmass : stateMass f = stateMass g) :
    f = g := by
  have hbracket : bracket f = bracket g :=
    (stateMass_eq_iff_bracket_eq f g).mp hmass
  have hcenter : f 1 = g 1 := by
    change f 1 - f 0 = g 1 - g 0 at hslope
    rw [hvalue] at hslope
    have h := congrArg (fun x : K => x + g 0) hslope
    simpa only [sub_add_cancel] using h
  apply eq_of_seed_eq_of_causalUnitBracket_eq hvalue hcenter
  intro n
  simpa only [discreteBracket_eq_causalUnitBracket] using congrFun hbracket n

theorem eq_iff_boundary_and_stateMass_eq (f g : ℕ → K) :
    f = g ↔
      f 0 = g 0 ∧ fdiff f 0 = fdiff g 0 ∧ stateMass f = stateMass g := by
  constructor
  · intro h
    subst g
    exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨hvalue, hslope, hmass⟩
    exact eq_of_boundary_and_stateMass_eq hvalue hslope hmass

@[simp] theorem stateMass_reconstruct (data : ReconstructionData K) :
    stateMass (reconstruct data) = data.projectiveMass.1 := by
  unfold stateMass
  rw [mk_bracket_reconstruct, toProjective_fromProjective]
  exact projectiveValveMass_projectiveValveCurvature data.projectiveMass.1 data.projectiveMass.2

def encode (f : ℕ → K) : ReconstructionData K where
  initialValue := f 0
  initialSlope := fdiff f 0
  projectiveMass := ⟨stateMass f, stateMass_constantCoeff f⟩

@[simp] theorem reconstruct_encode (f : ℕ → K) :
    reconstruct (encode f) = f := by
  apply eq_of_boundary_and_stateMass_eq
  · exact reconstruct_zero (encode f)
  · exact reconstruct_fdiff_zero (encode f)
  · exact stateMass_reconstruct (encode f)

@[simp] theorem encode_reconstruct (data : ReconstructionData K) :
    encode (reconstruct data) = data := by
  apply ReconstructionData.ext
  · exact reconstruct_zero data
  · exact reconstruct_fdiff_zero data
  · apply Subtype.ext
    exact stateMass_reconstruct data

/-- Exact classification of discrete states by boundary and projective mass. -/
def realDiscreteProjectiveReconstructionEquiv : (ℕ → K) ≃ ReconstructionData K where
  toFun := encode
  invFun := reconstruct
  left_inv := reconstruct_encode
  right_inv := encode_reconstruct

theorem encode_injective : Function.Injective (encode : (ℕ → K) → _) :=
  realDiscreteProjectiveReconstructionEquiv.injective

theorem existsUnique_state_of_boundary_and_mass (data : ReconstructionData K) :
    ∃! f : ℕ → K,
      f 0 = data.initialValue ∧
        fdiff f 0 = data.initialSlope ∧ stateMass f = data.projectiveMass.1 := by
  refine ⟨reconstruct data,
    ⟨reconstruct_zero data, reconstruct_fdiff_zero data,
      stateMass_reconstruct data⟩, ?_⟩
  intro f hf
  exact eq_of_boundary_and_stateMass_eq
    (hf.1.trans (reconstruct_zero data).symm)
    (hf.2.1.trans (reconstruct_fdiff_zero data).symm)
    (hf.2.2.trans (stateMass_reconstruct data).symm)

end

end GeometryOfNumbers.Analysis.DiscreteProjective
