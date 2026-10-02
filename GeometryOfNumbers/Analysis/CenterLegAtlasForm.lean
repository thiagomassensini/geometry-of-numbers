import GeometryOfNumbers.Analysis.AtlasEnergyPartition

/-!
# Center-leg synthesis after an explicitly admissible energy partition

Each base keeps its weighted camera channels, radial parameters and angles
until the existing local vector synthesis and quadratic readout are performed.
The atlas sums the resulting camera energies, never the camera vectors.
Conservation and the common radial factor are THEOREMS about this construction.
The partition is input data; no canonical cross-base rule has been derived.
-/

namespace GeometryOfNumbers.Analysis

open Geometry
open scoped BigOperators

noncomputable section

/-- Preserve every weighted base/channel state until its local energy readout. -/
def centerLegAtlasEnergy (P : AdmissibleAtlasPartition) (half : Nat)
    (q theta : AtlasBase → Nat → ℝ) (v : Nat → RealPlaneState) : ℝ :=
  ∑ b ∈ atlasActiveBases P half,
    centerLegCameraEnergy half (q b) (theta b) (fun r => atlasCoordinate P b r (v r))

theorem centerLegAtlasEnergy_eq_sum_cameras (P : AdmissibleAtlasPartition) (half : Nat)
    (q theta : AtlasBase → Nat → ℝ) (v : Nat → RealPlaneState) :
    centerLegAtlasEnergy P half q theta v =
      ∑ b ∈ atlasActiveBases P half,
        centerLegCameraEnergy half (q b) (theta b) (fun r => atlasCoordinate P b r (v r)) := rfl

theorem centerLegAtlasEnergy_eq_sum_local (P : AdmissibleAtlasPartition) (half : Nat)
    (q theta : AtlasBase → Nat → ℝ) (v : Nat → RealPlaneState) :
    centerLegAtlasEnergy P half q theta v =
      ∑ b ∈ atlasActiveBases P half, sumPositiveRadii half (fun r =>
        realPlaneEnergy (centerLegForm (q b r) (theta b r) (atlasCoordinate P b r (v r)))) := rfl

theorem centerLegAtlasEnergy_eq_factor (P : AdmissibleAtlasPartition) (half : Nat)
    (q theta : AtlasBase → Nat → ℝ) (v : Nat → RealPlaneState)
    (hq : ∀ b ∈ atlasActiveBases P half, ∀ r, 1 ≤ r → r ≤ half → q b r ≠ 0) :
    centerLegAtlasEnergy P half q theta v =
      ∑ b ∈ atlasActiveBases P half, sumPositiveRadii half (fun r =>
        ((q b r - 1) ^ 4 / q b r ^ 2) * (P.weight b r * realPlaneEnergy (v r))) := by
  unfold centerLegAtlasEnergy
  apply Finset.sum_congr rfl
  intro b hb
  rw [centerLegCameraEnergy_eq_factor half _ _ _ (hq b hb)]
  exact sumPositiveRadii_congr half _ _ (fun r _ _ => by rw [atlasCoordinate_energy])

/-- All local angles are independent, without hypotheses on radial parameters. -/
theorem centerLegAtlasEnergy_angle_independent (P : AdmissibleAtlasPartition) (half : Nat)
    (q theta₁ theta₂ : AtlasBase → Nat → ℝ) (v : Nat → RealPlaneState) :
    centerLegAtlasEnergy P half q theta₁ v = centerLegAtlasEnergy P half q theta₂ v := by
  apply Finset.sum_congr rfl
  intro b _
  exact centerLegCameraEnergy_angle_independent half _ _ _ _

theorem centerLegAtlasEnergy_nonneg (P : AdmissibleAtlasPartition) (half : Nat)
    (q theta : AtlasBase → Nat → ℝ) (v : Nat → RealPlaneState) :
    0 ≤ centerLegAtlasEnergy P half q theta v :=
  Finset.sum_nonneg (fun _ _ => centerLegCameraEnergy_nonneg half _ _ _)

/-- Zero cannot arise by cancellation between cameras or their local channels. -/
theorem centerLegAtlasEnergy_zero_iff_local_zero (P : AdmissibleAtlasPartition) (half : Nat)
    (q theta : AtlasBase → Nat → ℝ) (v : Nat → RealPlaneState) :
    centerLegAtlasEnergy P half q theta v = 0 ↔
      ∀ b ∈ atlasActiveBases P half, ∀ r, 1 ≤ r → r ≤ half →
        realPlaneEnergy (centerLegForm (q b r) (theta b r) (atlasCoordinate P b r (v r))) = 0 := by
  rw [centerLegAtlasEnergy, Finset.sum_eq_zero_iff_of_nonneg
    (fun _ _ => centerLegCameraEnergy_nonneg half _ _ _)]
  simp_rw [centerLegCameraEnergy_zero_iff_local_zero]

/-- First extract the common factor from the already constructed cameras. -/
theorem centerLegAtlasEnergy_common_eq_resolved (P : AdmissibleAtlasPartition) (half : Nat)
    (q : ℝ) (theta : AtlasBase → Nat → ℝ) (v : Nat → RealPlaneState) (hq : q ≠ 0) :
    centerLegAtlasEnergy P half (fun _ _ => q) theta v =
      ((q - 1) ^ 4 / q ^ 2) * atlasResolvedEnergy P half v := by
  unfold centerLegAtlasEnergy atlasResolvedEnergy
  simp_rw [centerLegCameraEnergy_common_eq_factor half q _ _ hq]
  exact (Finset.mul_sum _ _ _).symm

/-- Then use the partition's derived conservation of input energy. -/
theorem centerLegAtlasEnergy_common_eq_input (P : AdmissibleAtlasPartition) (half : Nat)
    (q : ℝ) (theta : AtlasBase → Nat → ℝ) (v : Nat → RealPlaneState) (hq : q ≠ 0) :
    centerLegAtlasEnergy P half (fun _ _ => q) theta v =
      ((q - 1) ^ 4 / q ^ 2) * sumPositiveRadii half (fun r => realPlaneEnergy (v r)) := by
  rw [centerLegAtlasEnergy_common_eq_resolved P half q theta v hq, atlasResolvedEnergy_eq_input]

/-- Admissible choices can differ; their common-defect energy is the same. -/
theorem centerLegAtlasEnergy_common_partition_independent
    (P₁ P₂ : AdmissibleAtlasPartition) (half : Nat) (q : ℝ)
    (theta₁ theta₂ : AtlasBase → Nat → ℝ) (v : Nat → RealPlaneState) (hq : q ≠ 0) :
    centerLegAtlasEnergy P₁ half (fun _ _ => q) theta₁ v =
      centerLegAtlasEnergy P₂ half (fun _ _ => q) theta₂ v := by
  rw [centerLegAtlasEnergy_common_eq_input P₁ half q theta₁ v hq,
    centerLegAtlasEnergy_common_eq_input P₂ half q theta₂ v hq]

/-- Positive total input energy suffices; zero-weight cameras are allowed. -/
theorem centerLegAtlasEnergy_common_zero_iff (P : AdmissibleAtlasPartition) (half : Nat)
    (q : ℝ) (theta : AtlasBase → Nat → ℝ) (v : Nat → RealPlaneState) (hq : q ≠ 0)
    (hv : 0 < sumPositiveRadii half (fun r => realPlaneEnergy (v r))) :
    centerLegAtlasEnergy P half (fun _ _ => q) theta v = 0 ↔ q = 1 := by
  rw [centerLegAtlasEnergy_common_eq_input P half q theta v hq]
  rw [← centerLegCameraEnergy_common_eq_factor half q (fun _ => 0) v hq]
  exact centerLegCameraEnergy_common_zero_iff half q _ v hq hv

theorem centerLegAtlasEnergy_zero_pairs (P : AdmissibleAtlasPartition)
    (q theta : AtlasBase → Nat → ℝ) (v : Nat → RealPlaneState) :
    centerLegAtlasEnergy P 0 q theta v = 0 := rfl

theorem centerLegAtlasEnergy_zero_input (P : AdmissibleAtlasPartition) (half : Nat)
    (q theta : AtlasBase → Nat → ℝ) :
    centerLegAtlasEnergy P half q theta (fun _ => (0, 0)) = 0 := by
  unfold centerLegAtlasEnergy
  apply Finset.sum_eq_zero
  intro b _
  unfold centerLegCameraEnergy
  calc
    _ = sumPositiveRadii half (fun _ => (0 : ℝ)) :=
      sumPositiveRadii_congr half _ _ (fun r _ _ => by
        rw [centerLegForm_energy_eq_closed, atlasCoordinate_energy]
        simp [realPlaneEnergy])
    _ = 0 := by rw [sumPositiveRadii_real_constant]; exact mul_zero _

end

end GeometryOfNumbers.Analysis
