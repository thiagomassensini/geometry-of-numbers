import GeometryOfNumbers.Geometry.ResidualTowerDepth
import GeometryOfNumbers.Geometry.CarryCenterLegCrosswalk
import GeometryOfNumbers.Foundation.ResidualPrefixRefinement

/-!
# The unique balanced channel carrying positive depth

Integer depth is the divisibility extension of the already proved natural
tower relation, not another tower or a maximum. At every positive level the
existing balanced decomposition selects the only possible offset. The level
remaining after this selection is exactly the depth of the aligned center.
Odd capacity is sufficient; primality and valuations are not used.
-/

namespace GeometryOfNumbers.Geometry

open Foundation
set_option autoImplicit false

/-- Extend the natural tower relation to signed arguments, after its power
characterization has been established. No integer tower is postulated. -/
def HasIntegerCarryDepthAtLeast (b : Nat) (x : Int) (depth : Nat) : Prop :=
  (b : Int) ^ depth ∣ x

theorem hasIntegerCarryDepthAtLeast_natCast_iff (b x depth : Nat) (hb : 0 < b) :
    HasIntegerCarryDepthAtLeast b (x : Int) depth ↔ HasCarryDepthAtLeast b x depth := by
  constructor
  · intro h
    apply (hasCarryDepthAtLeast_iff_dvd_pow b x depth hb).2
    apply Int.ofNat_dvd.mp
    exact (Int.natCast_pow b depth) ▸ h
  · intro h
    have hd := Int.ofNat_dvd.mpr ((hasCarryDepthAtLeast_iff_dvd_pow b x depth hb).1 h)
    change (b : Int) ^ depth ∣ (x : Int)
    rw [← Int.natCast_pow]
    exact hd

theorem hasIntegerCarryDepthAtLeast_zero_quantity (b depth : Nat) :
    HasIntegerCarryDepthAtLeast b 0 depth :=
  ⟨0, (Int.mul_zero _).symm⟩

theorem balancedCarry_sub_offset_eq_center (b n : Nat) (hodd : IsOddCapacity b) :
    (n : Int) - balancedCarryOffset b n hodd = balancedCarryCenter b n hodd := by
  have h := balancedCarry_reconstruction b n hodd
  omega

theorem balancedCarry_canonical_offset_depth_iff
    (b n depth : Nat) (hodd : IsOddCapacity b) :
    HasIntegerCarryDepthAtLeast b ((n : Int) - balancedCarryOffset b n hodd) depth ↔
      HasIntegerCarryDepthAtLeast b (balancedCarryCenter b n hodd) depth := by
  rw [balancedCarry_sub_offset_eq_center]

/-- Reuse geometric uniqueness with candidate center `n - offset`. -/
theorem balancedCarry_offset_unique_of_dvd (b n : Nat) (hodd : IsOddCapacity b)
    (offset : Int) (hbalanced : IsBalancedOffset b offset)
    (hdiv : (b : Int) ∣ (n : Int) - offset) :
    offset = balancedCarryOffset b n hodd := by
  have hvalue : (n : Int) = ((n : Int) - offset) + offset := by omega
  exact (balancedCarry_unique b n hodd ((n : Int) - offset) offset
    hvalue hdiv hbalanced).2

theorem capacity_dvd_power_of_positive (b depth : Nat) (hdepth : 0 < depth) :
    (b : Int) ∣ (b : Int) ^ depth := by
  cases depth with
  | zero => exact False.elim (Nat.lt_irrefl 0 hdepth)
  | succ depth =>
    refine ⟨(b : Int) ^ depth, ?_⟩
    rw [Int.pow_succ, Int.mul_comm]

theorem balancedCarry_positive_depth_iff (b n depth : Nat) (hodd : IsOddCapacity b)
    (hdepth : 0 < depth) (offset : Int) (hbalanced : IsBalancedOffset b offset) :
    HasIntegerCarryDepthAtLeast b ((n : Int) - offset) depth ↔
      offset = balancedCarryOffset b n hodd ∧
        HasIntegerCarryDepthAtLeast b (balancedCarryCenter b n hodd) depth := by
  constructor
  · intro hd
    have haligned : (b : Int) ∣ (n : Int) - offset :=
      Int.dvd_trans (capacity_dvd_power_of_positive b depth hdepth) hd
    have hoffset := balancedCarry_offset_unique_of_dvd b n hodd offset hbalanced haligned
    refine ⟨hoffset, ?_⟩
    rw [hoffset] at hd
    exact (balancedCarry_canonical_offset_depth_iff b n depth hodd).1 hd
  · intro h
    rw [h.1]
    exact (balancedCarry_canonical_offset_depth_iff b n depth hodd).2 h.2

theorem balancedCarry_offset_unique_of_positive_depth
    (b n depth : Nat) (hodd : IsOddCapacity b) (hdepth : 0 < depth)
    (offset : Int) (hbalanced : IsBalancedOffset b offset)
    (hd : HasIntegerCarryDepthAtLeast b ((n : Int) - offset) depth) :
    offset = balancedCarryOffset b n hodd :=
  ((balancedCarry_positive_depth_iff b n depth hodd hdepth offset hbalanced).1 hd).1

/-- The pre-valuation version of effective depth equals center depth: an
existential channel at any positive level is equivalent to center survival. -/
theorem balancedCarry_exists_depth_iff_center_depth
    (b n depth : Nat) (hodd : IsOddCapacity b) (hdepth : 0 < depth) :
    (∃ offset : Int, IsBalancedOffset b offset ∧
      HasIntegerCarryDepthAtLeast b ((n : Int) - offset) depth) ↔
        HasIntegerCarryDepthAtLeast b (balancedCarryCenter b n hodd) depth := by
  constructor
  · intro h
    rcases h with ⟨offset, hbalanced, hd⟩
    exact ((balancedCarry_positive_depth_iff b n depth hodd hdepth offset hbalanced).1 hd).2
  · intro hd
    exact ⟨balancedCarryOffset b n hodd, balancedCarry_offset_balanced b n hodd,
      (balancedCarry_canonical_offset_depth_iff b n depth hodd).2 hd⟩

theorem balancedCarry_unique_depth_witness
    (b n depth : Nat) (hodd : IsOddCapacity b) (hdepth : 0 < depth)
    (hd : HasIntegerCarryDepthAtLeast b (balancedCarryCenter b n hodd) depth) :
    ∃ offset : Int, IsBalancedOffset b offset ∧
      HasIntegerCarryDepthAtLeast b ((n : Int) - offset) depth ∧
        ∀ other : Int, IsBalancedOffset b other →
          HasIntegerCarryDepthAtLeast b ((n : Int) - other) depth → other = offset := by
  refine ⟨balancedCarryOffset b n hodd, balancedCarry_offset_balanced b n hodd,
    (balancedCarry_canonical_offset_depth_iff b n depth hodd).2 hd, ?_⟩
  intro other hbalanced hother
  exact balancedCarry_offset_unique_of_positive_depth b n depth hodd hdepth
    other hbalanced hother

/-- Identifies the same vertical index in the center relation and in the
already derived mass. It does not define a mass of `n` or of its center. -/
theorem balancedCarry_depth_and_mass_at_same_index
    (b n depth : Nat) (hodd : IsOddCapacity b)
    (hd : HasIntegerCarryDepthAtLeast b (balancedCarryCenter b n hodd) depth) :
    HasIntegerCarryDepthAtLeast b ((n : Int) - balancedCarryOffset b n hodd) depth ∧
      (canonicalResidualDepthMass b depth (oddCapacity_pos hodd)).numerator = 1 ∧
      (canonicalResidualDepthMass b depth (oddCapacity_pos hodd)).denominator = b ^ depth :=
  ⟨(balancedCarry_canonical_offset_depth_iff b n depth hodd).2 hd,
    canonicalResidualDepthMass_eq_unit_over_capacity b depth (oddCapacity_pos hodd)⟩

end GeometryOfNumbers.Geometry
