import Mathlib

namespace TiltSchurLastMoment
open scoped BigOperators
noncomputable section

theorem top_index_iff (s n : ℕ) (i j : Fin (n+1)) :
    s + i.val + j.val + 1 = s + 2*n + 1 ↔
      i = Fin.last n ∧ j = Fin.last n := by
  constructor
  · intro he
    have hi : i.val = n := by omega
    have hj : j.val = n := by omega
    exact ⟨Fin.ext hi, Fin.ext hj⟩
  · rintro ⟨hi,hj⟩
    rw [hi,hj]
    simp [Fin.val_last]
    omega

def changeLast (m : ℕ → ℝ) (s n : ℕ) (t : ℝ) (k : ℕ) : ℝ :=
  if k = s+2*n+1 then m k + t else m k

def weighted (m : ℕ → ℝ) (s n : ℕ) (v : Fin (n+1) → ℝ) : ℝ :=
  ∑ i : Fin (n+1), ∑ j : Fin (n+1),
    v i * v j *
      (((i.val+j.val+s:ℕ):ℝ)+1) *
      (2*((i.val+j.val+s:ℕ):ℝ)+3) *
      m (i.val+j.val+s+1)

private theorem last_indicator_sum (n : ℕ) (c : Fin (n+1) → Fin (n+1) → ℝ) :
    (∑ i : Fin (n+1), ∑ j : Fin (n+1),
      if i = Fin.last n ∧ j = Fin.last n then c i j else 0)
    = c (Fin.last n) (Fin.last n) := by
  simp only [ite_and]
  simp

theorem weighted_change_last (m : ℕ → ℝ) (s n : ℕ)
    (v : Fin (n+1) → ℝ) (t : ℝ) :
    weighted (changeLast m s n t) s n v =
      weighted m s n v +
        (v (Fin.last n))^2 *
          (((2*n+s:ℕ):ℝ)+1)*
            (2*((2*n+s:ℕ):ℝ)+3)*t := by
  have hpoint (i j : Fin (n+1)) :
      changeLast m s n t (i.val+j.val+s+1) =
        m (i.val+j.val+s+1) +
          (if i=Fin.last n ∧ j=Fin.last n then t else 0) := by
    unfold changeLast
    by_cases h : i = Fin.last n ∧ j = Fin.last n
    · rcases h with ⟨rfl, rfl⟩
      have heq : n+n+s = s+2*n := by omega
      simp [Fin.val_last, heq]
    · have htop : i.val+j.val+s ≠ s+2*n := by
        intro he
        apply h
        apply (top_index_iff s n i j).mp
        omega
      simp [htop, h]
  unfold weighted
  simp_rw [hpoint]
  simp_rw [mul_add]
  simp_rw [Finset.sum_add_distrib]
  simp only [mul_ite, mul_zero]
  rw [last_indicator_sum]
  simp [Fin.val_last]
  ring
  all_goals simp


/-- The last 2x2 moment gap is nonnegative under strict positivity of the
preceding moment and log-convexity at the final index. -/
def lastGap (m : ℕ → ℝ) (s n : ℕ) : ℝ :=
  m (s+2*n+1) - (m (s+2*n))^2 / m (s+2*n-1)

theorem lastGap_nonneg (m : ℕ → ℝ) (s n : ℕ)
    (hprev : 0 < m (s+2*n-1))
    (hlog : (m (s+2*n))^2 ≤
      m (s+2*n-1)*m (s+2*n+1)) :
    0 ≤ lastGap m s n := by
  unfold lastGap
  apply sub_nonneg.mpr
  apply (div_le_iff₀ hprev).mpr
  nlinarith [hlog]

/-- Removing the final nonnegative 2x2 gap gives a lower bound for
the full original weighted form, with no positivity of any new pivot. -/
theorem weighted_last_floor_le (m : ℕ → ℝ) (s n : ℕ)
    (v : Fin (n+1) → ℝ) (hgap : 0 ≤ lastGap m s n) :
    weighted (changeLast m s n (-(lastGap m s n))) s n v ≤
      weighted m s n v := by
  have eq := weighted_change_last m s n v (-(lastGap m s n))
  have hc : 0 ≤ (v (Fin.last n))^2 *
      (((2*n+s:ℕ):ℝ)+1)*(2*((2*n+s:ℕ):ℝ)+3) := by positivity
  nlinarith [mul_nonneg hc hgap]

/-- The new source-specific target: a positive old-moment floor
and the final 2x2 inequality imply positive full curvature. -/
theorem weighted_pos_of_last_floor_pos (m : ℕ → ℝ) (s n : ℕ)
    (v : Fin (n+1) → ℝ) (hgap : 0 ≤ lastGap m s n)
    (hfloor : 0 < weighted (changeLast m s n (-(lastGap m s n))) s n v) :
    0 < weighted m s n v :=
  lt_of_lt_of_le hfloor (weighted_last_floor_le m s n v hgap)

end
end TiltSchurLastMoment
