import CrossRadialPairing

namespace CarryCrossRadial
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd
open CarryEnergyCorrection CarryOddEnergy CarryMixedParity NativeLaguerre
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

/-- Exact TFVD reconstruction of BOTH complete source vectors, with independently
chosen radial regularizations and with both boundary traces and commutators. -/
theorem cross_source_reconstruction (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (k l : ℕ) (c d : ℕ →₀ ℂ) :
    physicalCompletedFiniteSource k c=
      completedSourceParts eta h0 h1 k c 0+completedSourceParts eta h0 h1 k c 1+
        completedSourceParts eta h0 h1 k c 2 ∧
    physicalCompletedFiniteSource l d=
      completedSourceParts eta h0 h1 l d 0+completedSourceParts eta h0 h1 l d 1+
        completedSourceParts eta h0 h1 l d 2 :=
  ⟨completed_source_three_parts eta h0 h1 k c, completed_source_three_parts eta h0 h1 l d⟩

/-- All NINE ordered bulk/boundary/commutator crosses; no residual is erased. -/
theorem cross_source_nine_pairings (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (k l : ℕ) (c d : ℕ →₀ ℂ) :
    crossSignedPair k l c d=
      ∑ a : Fin 3, ∑ b : Fin 3, canonicalCompletedNativeProjectiveChiralForm
        (completedSourceParts eta h0 h1 k c a) (completedSourceParts eta h0 h1 l d b) := by
  obtain ⟨hc,hd⟩ := cross_source_reconstruction eta h0 h1 k l c d
  unfold crossSignedPair
  rw [hc,hd]
  simp only [Fin.sum_univ_three, canonicalCompletedNativeProjectiveChiralForm,
    Prod.fst_add, Prod.snd_add, inner_add_left, inner_add_right]
  ring

/-- A literal readout of the reconstructed vectors, retaining all nine terms. -/
def crossGreenPair (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (k l : ℕ) (c d : ℕ →₀ ℂ) : ℂ :=
  ∑ a : Fin 3, ∑ b : Fin 3, canonicalCompletedNativeProjectiveChiralForm
    (completedSourceParts eta h0 h1 k c a) (completedSourceParts eta h0 h1 l d b)

theorem cross_green_eq_original (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (k l : ℕ) (c d : ℕ →₀ ℂ) :
    crossGreenPair eta h0 h1 k l c d=crossSignedPair k l c d :=
  (cross_source_nine_pairings eta h0 h1 k l c d).symm

/-- Bulk+boundary, both ordered crosses and residual-residual remain explicit.
No isotropy or regularity assumption is needed to preserve this identity. -/
theorem cross_green_four_blocks (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (k l : ℕ) (c d : ℕ →₀ ℂ) :
    crossSignedPair k l c d=
      canonicalCompletedNativeProjectiveChiralForm
        (completedSourceParts eta h0 h1 k c 0+completedSourceParts eta h0 h1 k c 1)
        (completedSourceParts eta h0 h1 l d 0+completedSourceParts eta h0 h1 l d 1)+
      canonicalCompletedNativeProjectiveChiralForm
        (completedSourceParts eta h0 h1 k c 0+completedSourceParts eta h0 h1 k c 1)
        (completedSourceParts eta h0 h1 l d 2)+
      canonicalCompletedNativeProjectiveChiralForm
        (completedSourceParts eta h0 h1 k c 2)
        (completedSourceParts eta h0 h1 l d 0+completedSourceParts eta h0 h1 l d 1)+
      canonicalCompletedNativeProjectiveChiralForm
        (completedSourceParts eta h0 h1 k c 2) (completedSourceParts eta h0 h1 l d 2) := by
  rw [cross_source_nine_pairings eta h0 h1 k l c d]
  simp only [Fin.sum_univ_three, canonicalCompletedNativeProjectiveChiralForm,
    Prod.fst_add, Prod.snd_add, inner_add_left, inner_add_right]
  ring

end
end CarryCrossRadial
