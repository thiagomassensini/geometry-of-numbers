import SigmaPadeCorrespondence
import SigmaSourceBezout

/-!
# Finite polynomial transport for the original C2 sigma minors

This module starts from the C4 source coefficients and the original
`completedSigmaLogJet`/`sigmaPadeD`. It introduces only the division-free
scaled sequence needed to transfer finite rational coefficient boxes.
-/

namespace CarrySigmaObstruction

open CarrySigmaSource
open CarrySigmaPade
open scoped BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- The division-free C4 scaling of the original source moments. The moment
sequence itself is still `2 * completedSigmaLogJet`. -/
def completedSigmaFiniteScaledMoment (d : ℝ) (n : ℕ) : ℝ :=
  completedSigmaDisplacedSourceCoefficient d 0 ^ (n + 1) *
    completedSigmaDisplacedMoment d n

/-- Coefficient form of the original C4 source identity, with the source
coefficient placed on the left of the convolution. -/
private theorem completedSigmaDisplacedMoment_source_recurrence (d : ℝ)
    (hd₁ : -(1 / 2 : ℝ) < d) (hd₂ : d < (1 / 2 : ℝ)) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1),
      completedSigmaDisplacedSourceCoefficient d j *
        completedSigmaDisplacedMoment d (n - j)) =
      -((n + 1 : ℝ) * completedSigmaDisplacedSourceCoefficient d (n + 1)) := by
  let c := completedSigmaDisplacedSourceCoefficient d
  let h := CarrySigmaSource.completedSigmaLogJet d
  have hsource := completedSigmaDisplacedSource_coefficient_recurrence d hd₁ hd₂ n
  have hreverse :
      (∑ j ∈ Finset.range (n + 1), c j * h (n - j)) =
        ∑ j ∈ Finset.range (n + 1), c (n - j) * h j := by
    refine Finset.sum_nbij' (fun j => n - j) (fun j => n - j) ?_ ?_ ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_range] at hj ⊢
      omega
    · intro j hj
      simp only [Finset.mem_range] at hj ⊢
      omega
    · intro j hj
      simp only [Finset.mem_range] at hj
      omega
    · intro j hj
      simp only [Finset.mem_range] at hj
      omega
    · intro j hj
      simp only [Finset.mem_range] at hj
      have hj' : n - (n - j) = j := by omega
      rw [hj']
  have hreverse' :
      (∑ j ∈ Finset.range (n + 1), c j * h (n - j)) =
        ∑ j ∈ Finset.range (n + 1), h j * c (n - j) := by
    rw [hreverse]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hconv :
      (∑ j ∈ Finset.range (n + 1), c j *
          completedSigmaDisplacedMoment d (n - j)) =
        2 * ∑ j ∈ Finset.range (n + 1), h j * c (n - j) := by
    calc
      _ = 2 * ∑ j ∈ Finset.range (n + 1), c j * h (n - j) := by
        simp only [completedSigmaDisplacedMoment]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = 2 * ∑ j ∈ Finset.range (n + 1), h j * c (n - j) := by rw [hreverse']
  rw [hconv]
  nlinarith [hsource]

/-- The C4 convolution recurrence becomes a polynomial recurrence after
scaling by powers of the source constant term. The sum is indexed by `j+1`
for `j ∈ range n`, i.e. the terms `j=1,...,n` in the usual notation. -/
theorem completedSigmaFiniteScaledMoment_recurrence (d : ℝ)
    (hd₁ : -(1 / 2 : ℝ) < d) (hd₂ : d < (1 / 2 : ℝ)) (n : ℕ) :
    completedSigmaFiniteScaledMoment d n =
      -((n + 1 : ℝ) * completedSigmaDisplacedSourceCoefficient d (n + 1) *
        completedSigmaDisplacedSourceCoefficient d 0 ^ n) -
      ∑ j ∈ Finset.range n,
        completedSigmaDisplacedSourceCoefficient d (j + 1) *
          completedSigmaFiniteScaledMoment d (n - (j + 1)) *
          completedSigmaDisplacedSourceCoefficient d 0 ^ j := by
  let c₀ := completedSigmaDisplacedSourceCoefficient d 0
  let c := completedSigmaDisplacedSourceCoefficient d
  let ell := completedSigmaDisplacedMoment d
  have hrec := completedSigmaDisplacedMoment_source_recurrence d hd₁ hd₂ n
  have hsplit :
      c 0 * ell n +
        ∑ j ∈ Finset.range n, c (j + 1) * ell (n - (j + 1)) =
        -((n + 1 : ℝ) * c (n + 1)) := by
    have h := hrec
    rw [Finset.sum_range_succ'] at h
    simpa [c, ell, add_comm] using h
  have hbase : c₀ * ell n =
      -((n + 1 : ℝ) * c (n + 1)) -
        ∑ j ∈ Finset.range n, c (j + 1) * ell (n - (j + 1)) := by
    linarith [hsplit]
  have hsum :
      c₀ ^ n * (∑ j ∈ Finset.range n,
        c (j + 1) * ell (n - (j + 1))) =
      ∑ j ∈ Finset.range n,
        c (j + 1) * completedSigmaFiniteScaledMoment d (n - (j + 1)) * c₀ ^ j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j < n := Finset.mem_range.mp hj
    have hexp : n - (j + 1) + 1 + j = n := by omega
    have hpow : c₀ ^ n = c₀ ^ (n - (j + 1) + 1) * c₀ ^ j := by
      calc
        c₀ ^ n = c₀ ^ ((n - (j + 1) + 1) + j) := by rw [hexp]
        _ = c₀ ^ (n - (j + 1) + 1) * c₀ ^ j := by rw [pow_add]
    dsimp [c, ell, c₀] at hpow ⊢
    rw [completedSigmaFiniteScaledMoment, hpow]
    ring
  calc
    completedSigmaFiniteScaledMoment d n = c₀ ^ n * (c₀ * ell n) := by
      simp [ell, c₀, completedSigmaFiniteScaledMoment, pow_succ]
      ring
    _ = c₀ ^ n *
          (-((n + 1 : ℝ) * c (n + 1)) -
            ∑ j ∈ Finset.range n, c (j + 1) * ell (n - (j + 1))) := by
      rw [hbase]
    _ = -((n + 1 : ℝ) * c (n + 1) * c₀ ^ n) -
          ∑ j ∈ Finset.range n,
            c (j + 1) * completedSigmaFiniteScaledMoment d (n - (j + 1)) * c₀ ^ j := by
      rw [mul_sub, hsum]
      ring
    _ = _ := by rfl

/-- The scaled source minor is exactly the original sigma Padé minor times
the positive C4 normalization factor. The right-hand side uses the original
`sigmaPadeD`. -/
theorem completedSigmaFiniteScaledMoment_minor_identity (d : ℝ) (s : ℕ) :
    completedSigmaFiniteScaledMoment d s *
        completedSigmaFiniteScaledMoment d (s + 2) -
      (completedSigmaFiniteScaledMoment d (s + 1)) ^ 2 =
      4 * completedSigmaDisplacedSourceCoefficient d 0 ^ (2 * s + 4) *
        sigmaPadeD d s := by
  simp only [completedSigmaFiniteScaledMoment, completedSigmaDisplacedMoment,
    sigmaPadeD]
  have hpow₁ :
      completedSigmaDisplacedSourceCoefficient d 0 ^ (s + 1) *
        completedSigmaDisplacedSourceCoefficient d 0 ^ (s + 3) =
      completedSigmaDisplacedSourceCoefficient d 0 ^ (2 * s + 4) := by
    rw [← pow_add]
    congr 1
    omega
  have hpow₂ :
      (completedSigmaDisplacedSourceCoefficient d 0 ^ (s + 2)) ^ 2 =
        completedSigmaDisplacedSourceCoefficient d 0 ^ (2 * s + 4) := by
    rw [← pow_mul]
    congr 1
    omega
  calc
    _ =
        (completedSigmaDisplacedSourceCoefficient d 0 ^ (s + 1) *
            completedSigmaDisplacedSourceCoefficient d 0 ^ (s + 3)) *
            (2 * CarrySigmaSource.completedSigmaLogJet d s) *
            (2 * CarrySigmaSource.completedSigmaLogJet d (s + 2)) -
          (completedSigmaDisplacedSourceCoefficient d 0 ^ (s + 2)) ^ 2 *
            (2 * CarrySigmaSource.completedSigmaLogJet d (s + 1)) ^ 2 := by
      ring
    _ =
        completedSigmaDisplacedSourceCoefficient d 0 ^ (2 * s + 4) *
          (4 * CarrySigmaSource.completedSigmaLogJet d s *
              CarrySigmaSource.completedSigmaLogJet d (s + 2) -
            4 * (CarrySigmaSource.completedSigmaLogJet d (s + 1)) ^ 2) := by
      rw [hpow₁, hpow₂]
      ring
    _ = _ := by ring

theorem sigmaPadeD_pos_of_completedSigmaFiniteScaledMoment_minor_pos
    (d : ℝ) (hd₁ : -(1 / 2 : ℝ) < d) (hd₂ : d < (1 / 2 : ℝ)) (s : ℕ)
    (hminor : 0 < completedSigmaFiniteScaledMoment d s *
      completedSigmaFiniteScaledMoment d (s + 2) -
        (completedSigmaFiniteScaledMoment d (s + 1)) ^ 2) :
    0 < sigmaPadeD d s := by
  have hc₀ := completedSigmaDisplacedSourceCoefficient_zero_pos d hd₁ hd₂
  have hscale : 0 < 4 * completedSigmaDisplacedSourceCoefficient d 0 ^ (2 * s + 4) :=
    mul_pos (by norm_num) (pow_pos hc₀ _)
  have hidentity := completedSigmaFiniteScaledMoment_minor_identity d s
  rw [hidentity] at hminor
  by_contra hnot
  have hnonpos : sigmaPadeD d s ≤ 0 := le_of_not_gt hnot
  have hscaled := mul_nonpos_of_nonneg_of_nonpos hscale.le hnonpos
  linarith

theorem sigmaPadeD_neg_of_completedSigmaFiniteScaledMoment_minor_neg
    (d : ℝ) (hd₁ : -(1 / 2 : ℝ) < d) (hd₂ : d < (1 / 2 : ℝ)) (s : ℕ)
    (hminor : completedSigmaFiniteScaledMoment d s *
      completedSigmaFiniteScaledMoment d (s + 2) -
        (completedSigmaFiniteScaledMoment d (s + 1)) ^ 2 < 0) :
    sigmaPadeD d s < 0 := by
  have hc₀ := completedSigmaDisplacedSourceCoefficient_zero_pos d hd₁ hd₂
  have hscale : 0 < 4 * completedSigmaDisplacedSourceCoefficient d 0 ^ (2 * s + 4) :=
    mul_pos (by norm_num) (pow_pos hc₀ _)
  have hidentity := completedSigmaFiniteScaledMoment_minor_identity d s
  rw [hidentity] at hminor
  by_contra hnot
  have hnonneg : 0 ≤ sigmaPadeD d s := le_of_not_gt hnot
  have hscaled := mul_nonneg hscale.le hnonneg
  linarith

end
end CarrySigmaObstruction
