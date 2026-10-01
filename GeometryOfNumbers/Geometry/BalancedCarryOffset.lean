import GeometryOfNumbers.Foundation.EmergentCycleTransport

/-! One-cell balanced coordinates obtained from the existing stepping/reset
coordinates, not a quotient/remainder API. Oddness excludes the antipodal tie;
no prime capacity, midpoint division or historical dependency is used. -/

namespace GeometryOfNumbers.Geometry

open Foundation

set_option autoImplicit false

/-- Explicit oddness data, without a remainder or a half-capacity division. -/
def IsOddCapacity (b : Nat) : Prop := ∃ half : Nat, b = 2 * half + 1

/-- Strict half-cell bounds, expressed by signed doubling. -/
def IsBalancedOffset (b : Nat) (offset : Int) : Prop :=
  -(b : Int) < 2 * offset ∧ 2 * offset < (b : Int)

theorem oddCapacity_pos {b : Nat} (hodd : IsOddCapacity b) : 0 < b := by
  rcases hodd with ⟨half, h⟩
  omega

theorem oddCapacity_no_antipodal {b : Nat} (hodd : IsOddCapacity b) (r : Nat) :
    2 * r ≠ b := by
  rcases hodd with ⟨half, h⟩
  omega

theorem oddCapacity_residual_side {b : Nat} (hodd : IsOddCapacity b) (r : Nat) :
    2 * r < b ∨ b < 2 * r := by
  have hne := oddCapacity_no_antipodal hodd r
  by_cases hlow : 2 * r < b
  · exact Or.inl hlow
  · exact Or.inr (by omega)

/-- The oddness argument restricts the domain: no even tie is assigned a side. -/
def balancedCarryOffset (b n : Nat) (_hodd : IsOddCapacity b) : Int :=
  let residual := cycleResidual b n
  if 2 * residual < b then (residual : Int) else (residual : Int) - (b : Int)

def balancedCarryCenter (b n : Nat) (_hodd : IsOddCapacity b) : Int :=
  let cycles := completedCycleCount b n
  let residual := cycleResidual b n
  if 2 * residual < b then ((cycles * b : Nat) : Int)
  else (((cycles + 1) * b : Nat) : Int)

theorem balancedCarry_reconstruction (b n : Nat) (hodd : IsOddCapacity b) :
    (n : Int) = balancedCarryCenter b n hodd + balancedCarryOffset b n hodd := by
  have hvalue := congrArg (fun x : Nat => (x : Int))
    (cycleCoordinatesRec_spec b (oddCapacity_pos hodd) n).1
  rw [Int.natCast_add] at hvalue
  unfold balancedCarryCenter balancedCarryOffset
  dsimp only
  by_cases hlow : 2 * cycleResidual b n < b
  · rw [if_pos hlow, if_pos hlow]
    exact hvalue
  · rw [if_neg hlow, if_neg hlow, Nat.succ_mul, Int.natCast_add]
    omega

theorem balancedCarry_center_aligned (b n : Nat) (hodd : IsOddCapacity b) :
    (b : Int) ∣ balancedCarryCenter b n hodd := by
  unfold balancedCarryCenter
  dsimp only
  by_cases hlow : 2 * cycleResidual b n < b
  · rw [if_pos hlow, Int.natCast_mul]
    exact ⟨(completedCycleCount b n : Int), Int.mul_comm _ _⟩
  · rw [if_neg hlow, Int.natCast_mul]
    exact ⟨((completedCycleCount b n + 1 : Nat) : Int), Int.mul_comm _ _⟩

theorem balancedCarry_offset_balanced (b n : Nat) (hodd : IsOddCapacity b) :
    IsBalancedOffset b (balancedCarryOffset b n hodd) := by
  have hr := (cycleCoordinatesRec_spec b (oddCapacity_pos hodd) n).2
  have hb := oddCapacity_pos hodd
  unfold balancedCarryOffset IsBalancedOffset
  dsimp only
  by_cases hlow : 2 * cycleResidual b n < b
  · rw [if_pos hlow]
    constructor <;> omega
  · have hhigh : b < 2 * cycleResidual b n := by
      rcases oddCapacity_residual_side hodd (cycleResidual b n) with h | h
      · exact False.elim (hlow h)
      · exact h
    rw [if_neg hlow]
    constructor <;> omega

theorem balancedOffset_iff_natAbs (b : Nat) (offset : Int) :
    IsBalancedOffset b offset ↔ 2 * offset.natAbs < b := by
  unfold IsBalancedOffset
  constructor
  · intro h
    by_cases hn : 0 ≤ offset
    · have habs := Int.natAbs_of_nonneg hn
      omega
    · have hnneg : 0 ≤ -offset := by omega
      have habs := Int.natAbs_of_nonneg hnneg
      rw [Int.natAbs_neg] at habs
      omega
  · intro h
    by_cases hn : 0 ≤ offset
    · have habs := Int.natAbs_of_nonneg hn
      constructor <;> omega
    · have hnneg : 0 ≤ -offset := by omega
      have habs := Int.natAbs_of_nonneg hnneg
      rw [Int.natAbs_neg] at habs
      constructor <;> omega

theorem balancedCarry_offset_natAbs_bound (b n : Nat) (hodd : IsOddCapacity b) :
    2 * (balancedCarryOffset b n hodd).natAbs < b :=
  (balancedOffset_iff_natAbs _ _).1 (balancedCarry_offset_balanced b n hodd)

/-- Uniqueness needs no oddness: strict representatives, whenever they exist,
cannot differ by a nonzero capacity multiple. Oddness is used for existence. -/
theorem balancedCenterOffset_unique {b : Nat} {n c₁ a₁ c₂ a₂ : Int}
    (h₁ : n = c₁ + a₁) (h₂ : n = c₂ + a₂)
    (hc₁ : (b : Int) ∣ c₁) (hc₂ : (b : Int) ∣ c₂)
    (ha₁ : IsBalancedOffset b a₁) (ha₂ : IsBalancedOffset b a₂) :
    c₁ = c₂ ∧ a₁ = a₂ := by
  have noPositiveDifference (hpos : 0 < c₁ - c₂) : False := by
    have hlarge := Int.le_of_dvd hpos (Int.dvd_sub hc₁ hc₂)
    unfold IsBalancedOffset at ha₁ ha₂
    omega
  have noNegativeDifference (hpos : 0 < c₂ - c₁) : False := by
    have hlarge := Int.le_of_dvd hpos (Int.dvd_sub hc₂ hc₁)
    unfold IsBalancedOffset at ha₁ ha₂
    omega
  have hc : c₁ = c₂ := by
    by_cases hlt : c₁ < c₂
    · exact False.elim (noNegativeDifference (by omega))
    · by_cases hgt : c₂ < c₁
      · exact False.elim (noPositiveDifference (by omega))
      · omega
  exact ⟨hc, by omega⟩

theorem balancedCarry_unique (b n : Nat) (hodd : IsOddCapacity b)
    (center offset : Int) (hvalue : (n : Int) = center + offset)
    (haligned : (b : Int) ∣ center) (hbalanced : IsBalancedOffset b offset) :
    center = balancedCarryCenter b n hodd ∧ offset = balancedCarryOffset b n hodd :=
  balancedCenterOffset_unique hvalue (balancedCarry_reconstruction b n hodd)
    haligned (balancedCarry_center_aligned b n hodd)
    hbalanced (balancedCarry_offset_balanced b n hodd)

theorem balancedCarry_zero_residual (b n : Nat) (hodd : IsOddCapacity b)
    (hzero : cycleResidual b n = 0) :
    balancedCarryOffset b n hodd = 0 ∧ balancedCarryCenter b n hodd = (n : Int) := by
  have hb := oddCapacity_pos hodd
  have hlow : 2 * cycleResidual b n < b := by rw [hzero]; omega
  have hoffset : balancedCarryOffset b n hodd = 0 := by
    unfold balancedCarryOffset
    dsimp only
    rw [if_pos hlow, hzero]
    rfl
  have hvalue := balancedCarry_reconstruction b n hodd
  exact ⟨hoffset, by rw [hoffset] at hvalue; omega⟩

theorem balancedCarry_nonzero_residual (b n : Nat) (hodd : IsOddCapacity b)
    (hzero : cycleResidual b n ≠ 0) :
    balancedCarryOffset b n hodd ≠ 0 ∧ (n : Int) ≠ balancedCarryCenter b n hodd := by
  have hr := (cycleCoordinatesRec_spec b (oddCapacity_pos hodd) n).2
  have hoffset : balancedCarryOffset b n hodd ≠ 0 := by
    unfold balancedCarryOffset
    dsimp only
    by_cases hlow : 2 * cycleResidual b n < b
    · rw [if_pos hlow]
      omega
    · rw [if_neg hlow]
      omega
  have hvalue := balancedCarry_reconstruction b n hodd
  exact ⟨hoffset, by omega⟩

/-- The antipodal C2 quantity has no strictly balanced aligned decomposition. -/
theorem antipodal_two_no_strict_decomposition (center offset : Int)
    (hvalue : (1 : Int) = center + offset) (haligned : (2 : Int) ∣ center) :
    ¬ IsBalancedOffset 2 offset := by
  intro hbalanced
  unfold IsBalancedOffset at hbalanced
  have hoffset : offset = 0 := by omega
  have hcenter : center = 1 := by omega
  rw [hcenter] at haligned
  rcases haligned with ⟨factor, hfactor⟩
  omega

/-- If the boundary is allowed, both antipodal branches are valid and distinct. -/
theorem antipodal_two_boundary_nonunique :
    (1 : Int) = 0 + 1 ∧ (1 : Int) = 2 + (-1) ∧
    (2 : Int) ∣ 0 ∧ (2 : Int) ∣ 2 ∧
    2 * (1 : Int).natAbs = 2 ∧ 2 * (-1 : Int).natAbs = 2 ∧
    (0 : Int) ≠ 2 :=
  ⟨rfl, rfl, ⟨0, rfl⟩, ⟨1, rfl⟩, rfl, rfl, by decide⟩

end GeometryOfNumbers.Geometry
