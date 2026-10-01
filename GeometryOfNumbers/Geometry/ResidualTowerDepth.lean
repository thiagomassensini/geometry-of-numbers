import GeometryOfNumbers.Foundation.EmergentResidualTower

/-!
# Depth as successive zero residuals

This conservative API extension lives outside the frozen Foundation. Its
definition inspects the existing tower, not divisibility or a valuation.
Only after reconstruction and uniqueness do powers characterize the relation.
Zero and capacity one can survive every level; no maximum is constructed.
-/

namespace GeometryOfNumbers.Geometry

open Foundation
set_option autoImplicit false

/-- All resolved positions are zero; the unresolved tail is unrestricted. -/
def ResidualTowerZeroPrefix : {depth : Nat} → ResidualTowerCoordinates depth → Prop
  | 0, _ => True
  | _ + 1, (residual, rest) => residual = 0 ∧ ResidualTowerZeroPrefix rest

/-- Survival of `depth` successive residual extractions in the actual tower.
Its carry interpretation requires positive capacity. -/
def HasCarryDepthAtLeast (b x depth : Nat) : Prop :=
  ResidualTowerZeroPrefix (emergentResidualTower b depth x)

theorem hasCarryDepthAtLeast_zero (b x : Nat) : HasCarryDepthAtLeast b x 0 :=
  True.intro

theorem hasCarryDepthAtLeast_succ (b x depth : Nat) :
    HasCarryDepthAtLeast b x (depth + 1) ↔
      cycleResidual b x = 0 ∧
        HasCarryDepthAtLeast b (completedCycleCount b x) depth := Iff.rfl

theorem residualTowerZeroPrefix_iff_prefixValue_zero (b depth : Nat)
    (hb : 0 < b) (coordinates : ResidualTowerCoordinates depth) :
    ResidualTowerZeroPrefix coordinates ↔ residualTowerPrefixValue b coordinates = 0 := by
  induction depth with
  | zero => exact ⟨fun _ => rfl, fun _ => True.intro⟩
  | succ depth ih =>
    rcases coordinates with ⟨residual, rest⟩
    constructor
    · intro h
      change residualTowerPrefixValue b rest * b + residual = 0
      rw [(ih rest).1 h.2, h.1, Nat.zero_mul]
    · intro h
      have hparts := Nat.add_eq_zero_iff.mp h
      have hprefix : residualTowerPrefixValue b rest = 0 := by
        cases Nat.mul_eq_zero.mp hparts.1 with
        | inl hz => exact hz
        | inr hz => exact False.elim (Nat.lt_irrefl 0 (hz ▸ hb))
      exact ⟨hparts.2, (ih rest).2 hprefix⟩

theorem hasCarryDepthAtLeast_iff_prefixValue_zero (b x depth : Nat) (hb : 0 < b) :
    HasCarryDepthAtLeast b x depth ↔
      residualTowerPrefixValue b (emergentResidualTower b depth x) = 0 :=
  residualTowerZeroPrefix_iff_prefixValue_zero b depth hb _

theorem hasCarryDepthAtLeast_eq_scaled_tail (b x depth : Nat) (hb : 0 < b)
    (hdepth : HasCarryDepthAtLeast b x depth) :
    x = residualTowerTail (emergentResidualTower b depth x) * b ^ depth := by
  have hexpansion := emergentResidualTower_expansion b depth x hb
  rw [(hasCarryDepthAtLeast_iff_prefixValue_zero b x depth hb).1 hdepth,
    Nat.zero_add] at hexpansion
  exact hexpansion

-- A comparison tuple for the existing uniqueness theorem, not new dynamics.
private def zeroPrefixCoordinates : (depth : Nat) → Nat → ResidualTowerCoordinates depth
  | 0, tail => tail
  | depth + 1, tail => (0, zeroPrefixCoordinates depth tail)

private theorem zeroPrefixCoordinates_bounded (b depth tail : Nat) (hb : 0 < b) :
    BoundedResidualTower b (zeroPrefixCoordinates depth tail) := by
  induction depth with
  | zero => exact True.intro
  | succ depth ih => exact ⟨hb, ih⟩

private theorem zeroPrefixCoordinates_zero (depth tail : Nat) :
    ResidualTowerZeroPrefix (zeroPrefixCoordinates depth tail) := by
  induction depth with
  | zero => exact True.intro
  | succ depth ih => exact ⟨rfl, ih⟩

private theorem zeroPrefixCoordinates_tail (depth tail : Nat) :
    residualTowerTail (zeroPrefixCoordinates depth tail) = tail := by
  induction depth with
  | zero => rfl
  | succ depth ih => exact ih

theorem hasCarryDepthAtLeast_iff_dvd_pow (b x depth : Nat) (hb : 0 < b) :
    HasCarryDepthAtLeast b x depth ↔ b ^ depth ∣ x := by
  constructor
  · intro hdepth
    refine ⟨residualTowerTail (emergentResidualTower b depth x), ?_⟩
    exact (hasCarryDepthAtLeast_eq_scaled_tail b x depth hb hdepth).trans
      (Nat.mul_comm _ _)
  · intro hdiv
    rcases hdiv with ⟨tail, htail⟩
    have hprefix := (residualTowerZeroPrefix_iff_prefixValue_zero b depth hb
      (zeroPrefixCoordinates depth tail)).1 (zeroPrefixCoordinates_zero depth tail)
    have hvalue : residualTowerValue b (zeroPrefixCoordinates depth tail) = x := by
      rw [residualTowerValue_eq_prefix_add_scaled_tail b depth, hprefix,
        zeroPrefixCoordinates_tail, Nat.zero_add, Nat.mul_comm]
      exact htail.symm
    have hcanonical := residualTower_eq_canonical b depth x hb
      (zeroPrefixCoordinates depth tail) (zeroPrefixCoordinates_bounded b depth tail hb) hvalue
    change ResidualTowerZeroPrefix (emergentResidualTower b depth x)
    rw [← hcanonical]
    exact zeroPrefixCoordinates_zero depth tail

theorem hasCarryDepthAtLeast_zero_quantity (b depth : Nat) (hb : 0 < b) :
    HasCarryDepthAtLeast b 0 depth :=
  (hasCarryDepthAtLeast_iff_dvd_pow b 0 depth hb).2 ⟨0, (Nat.mul_zero _).symm⟩

theorem hasCarryDepthAtLeast_capacity_one (x depth : Nat) :
    HasCarryDepthAtLeast 1 x depth := by
  apply (hasCarryDepthAtLeast_iff_dvd_pow 1 x depth (Nat.zero_lt_succ 0)).2
  rw [Nat.one_pow]
  exact Nat.one_dvd x

/-- Total raw recursion at capacity zero is not a valid positive-capacity carry
model: its zero-prefix test cannot be interpreted by divisibility. -/
theorem zeroCapacity_depth_does_not_characterize_divisibility :
    HasCarryDepthAtLeast 0 1 1 ∧ ¬ (0 ^ 1 ∣ (1 : Nat)) := by
  constructor
  · exact ⟨rfl, True.intro⟩
  · intro h
    rcases h with ⟨q, hq⟩
    change 1 = 0 * q at hq
    rw [Nat.zero_mul] at hq
    exact Nat.zero_ne_one hq.symm

end GeometryOfNumbers.Geometry
