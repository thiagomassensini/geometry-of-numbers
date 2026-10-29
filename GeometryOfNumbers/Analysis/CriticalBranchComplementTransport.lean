import GeometryOfNumbers.Analysis.GreenParsevalMaterialLogOperator

/-!
# The real polarized compression complement of the existing C2 source

The complement acts on a whole synthesized vector. The material clock is
evaluated only on its existing maximal domain. Parseval transports this SAME
complement; raw Green analysis adds its frame defect. No chiral identification
or strict sign is assumed here.
-/
noncomputable section
open scoped InnerProductSpace BigOperators

namespace GeometryOfNumbers.Analysis.CriticalBranchComplement

section RealHilbert
variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]

/-- Orthogonal escape from the range of the original isometry. -/
def complement (U : E →ₗᵢ[ℝ] F) : F →L[ℝ] F :=
  1 - U.toContinuousLinearMap ∘L U.toContinuousLinearMap.adjoint

theorem complement_apply (U : E →ₗᵢ[ℝ] F) (z : F) :
    complement U z = z - U (U.toContinuousLinearMap.adjoint z) := rfl

/-- Two independent inputs, before any diagonal specialization. -/
theorem complement_pairing (U : E →ₗᵢ[ℝ] F) (z w : F) :
    inner ℝ (complement U z) (complement U w) = inner ℝ z w -
      inner ℝ (U.toContinuousLinearMap.adjoint z) (U.toContinuousLinearMap.adjoint w) := by
  rw [complement_apply, complement_apply, inner_sub_left, inner_sub_right,
    inner_sub_right, U.inner_map_map]
  have hl : inner ℝ (U (U.toContinuousLinearMap.adjoint z)) w =
      inner ℝ (U.toContinuousLinearMap.adjoint z) (U.toContinuousLinearMap.adjoint w) :=
    (U.toContinuousLinearMap.adjoint_inner_right _ _).symm
  have hr : inner ℝ z (U (U.toContinuousLinearMap.adjoint w)) =
      inner ℝ (U.toContinuousLinearMap.adjoint z) (U.toContinuousLinearMap.adjoint w) :=
    (U.toContinuousLinearMap.adjoint_inner_left _ _).symm
  rw [hl, hr]
  ring

theorem compression_energy (U : E →ₗᵢ[ℝ] F) (z : F) :
    ‖z‖^2 - ‖U.toContinuousLinearMap.adjoint z‖^2 = ‖complement U z‖^2 := by
  simpa only [real_inner_self_eq_norm_sq] using (complement_pairing U z z).symm

/-- Strictness is a separate non-collapse condition on the actual escape. -/
theorem compression_energy_pos_iff (U : E →ₗᵢ[ℝ] F) (z : F) :
    0 < ‖z‖^2 - ‖U.toContinuousLinearMap.adjoint z‖^2 ↔ complement U z ≠ 0 := by
  rw [compression_energy, sq_pos_iff, norm_ne_zero_iff]

/-- Finite synthesis precedes the form; every ordered cross survives. -/
theorem complement_synthesis_pairing (U : E →ₗᵢ[ℝ] F) {N M : ℕ}
    (z : Fin N → F) (w : Fin M → F) (a : Fin N → ℝ) (b : Fin M → ℝ) :
    inner ℝ (complement U (∑ i, a i • z i)) (complement U (∑ j, b j • w j)) =
      ∑ i, ∑ j, a i * b j * inner ℝ (complement U (z i)) (complement U (w j)) := by
  simp only [map_sum, map_smul, sum_inner, inner_sum, real_inner_smul_left,
    real_inner_smul_right]
  rw [Finset.sum_comm]
  congr 1
  funext i
  congr 1
  funext j
  ring

theorem compression_energy_nonneg (U : E →ₗᵢ[ℝ] F) (z : F) :
    0 ≤ ‖z‖^2 - ‖U.toContinuousLinearMap.adjoint z‖^2 := by
  rw [compression_energy]
  positivity

/-- Exact transport under a second isometry, including the new adjoint. -/
theorem complement_isometric_transport (U : E →ₗᵢ[ℝ] F) (P : F →ₗᵢ[ℝ] G) (z : F) :
    complement (P.comp U) (P z) = P (complement U z) := by
  have hp : P.toContinuousLinearMap.adjoint (P z) = z := by
    have h := congrArg (fun A : F →L[ℝ] F => A z) P.adjoint_comp_self
    exact h
  have hc : (P.comp U).toContinuousLinearMap =
      P.toContinuousLinearMap ∘L U.toContinuousLinearMap := rfl
  simp only [complement_apply, hc, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.comp_apply, hp, map_sub]
  rfl

theorem complement_isometric_pairing (U : E →ₗᵢ[ℝ] F) (P : F →ₗᵢ[ℝ] G) (z w : F) :
    inner ℝ (complement (P.comp U) (P z)) (complement (P.comp U) (P w)) =
      inner ℝ (complement U z) (complement U w) := by
  rw [complement_isometric_transport, complement_isometric_transport, P.inner_map_map]

end RealHilbert

open GreenFrame.Concrete C2GlobalGreenBridge GreenStateMaterialLog GreenParsevalMaterialLog
open C2GreenWhiteningGenealogy

/-- The existing canonical Parseval analysis, with its original metric,
restricted to real scalars. This abbreviation introduces no new operator. -/
def realParseval : State →ₗᵢ[ℝ] ConcreteAnalysisSpace :=
  { greenParsevalAnalysis.restrictScalars ℝ with
    norm_map' := canonicalGreenAnalysis_norm }

/-- The material clock is evaluated only at a source in its actual domain. -/
theorem c2_clock_compression_energy (t : ℝ) (v : CoreState)
    (hv : c2GlobalGreenInputIsometry t v ∈ greenStateMaterialLogGenerator.domain) :
    ‖greenStateMaterialLogGenerator ⟨c2GlobalGreenInputIsometry t v,hv⟩‖^2 -
      ‖(c2GlobalGreenInputIsometry t).toContinuousLinearMap.adjoint
        (greenStateMaterialLogGenerator ⟨c2GlobalGreenInputIsometry t v,hv⟩)‖^2 =
    ‖complement (c2GlobalGreenInputIsometry t)
      (greenStateMaterialLogGenerator ⟨c2GlobalGreenInputIsometry t v,hv⟩)‖^2 :=
  compression_energy _ _

/-- Both clocked inputs retain their real polarization under Parseval.
The domain assumptions are independent; no application of L² is needed. -/
theorem c2_clock_complement_parseval_pairing (t : ℝ) (v w : CoreState)
    (hv : c2GlobalGreenInputIsometry t v ∈ greenStateMaterialLogGenerator.domain)
    (hw : c2GlobalGreenInputIsometry t w ∈ greenStateMaterialLogGenerator.domain) :
    inner ℝ
      (complement (realParseval.comp (c2GlobalGreenInputIsometry t))
        (greenParsevalMaterialLogOperator
          ⟨greenParsevalAnalysis (c2GlobalGreenInputIsometry t v),
            greenParsevalMaterialLogOperator_c2Source_mem_domain t v hv⟩))
      (complement (realParseval.comp (c2GlobalGreenInputIsometry t))
        (greenParsevalMaterialLogOperator
          ⟨greenParsevalAnalysis (c2GlobalGreenInputIsometry t w),
            greenParsevalMaterialLogOperator_c2Source_mem_domain t w hw⟩)) =
    inner ℝ
      (complement (c2GlobalGreenInputIsometry t)
        (greenStateMaterialLogGenerator ⟨c2GlobalGreenInputIsometry t v,hv⟩))
      (complement (c2GlobalGreenInputIsometry t)
        (greenStateMaterialLogGenerator ⟨c2GlobalGreenInputIsometry t w,hw⟩)) := by
  rw [greenParsevalMaterialLogOperator_c2Source_intertwining,
    greenParsevalMaterialLogOperator_c2Source_intertwining]
  exact complement_isometric_pairing _ realParseval _ _

/-- Raw Green retains a literal polarized frame residual on the SAME states.
This equality makes no claim that the residual vanishes or has either sign. -/
theorem rawGreen_complement_pairing (t : ℝ) (z w : State) :
    inner ℝ (canonicalRawGreenAnalysis (complement (c2GlobalGreenInputIsometry t) z))
      (canonicalRawGreenAnalysis (complement (c2GlobalGreenInputIsometry t) w)) =
    inner ℝ (complement (c2GlobalGreenInputIsometry t) z)
      (complement (c2GlobalGreenInputIsometry t) w) +
    inner ℝ
      ((((canonicalRawGreenAnalysis.restrictScalars ℝ).adjoint ∘L
        canonicalRawGreenAnalysis.restrictScalars ℝ) - 1)
          (complement (c2GlobalGreenInputIsometry t) z))
      (complement (c2GlobalGreenInputIsometry t) w) := by
  rw [sub_apply, one_apply_eq_self,
    inner_sub_left, ContinuousLinearMap.comp_apply,
    (canonicalRawGreenAnalysis.restrictScalars ℝ).adjoint_inner_left]
  change _ = _ + (inner ℝ
    (canonicalRawGreenAnalysis (complement (c2GlobalGreenInputIsometry t) z))
    (canonicalRawGreenAnalysis (complement (c2GlobalGreenInputIsometry t) w)) - _)
  ring

end GeometryOfNumbers.Analysis.CriticalBranchComplement
