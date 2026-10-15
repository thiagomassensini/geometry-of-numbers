import GeometryOfNumbers.Geometry.ResidualTowerDepth
import GeometryOfNumbers.Geometry.CenterLegReflection

/-! Integer incidences BEFORE any quadratic realization. A cell is a camera
presentation, not a new intrinsic quantity. Its radius is the scale b^k;
its three positions use the existing integer center/leg geometry. No odd
balanced-offset convention or maximal-depth function is introduced. -/
namespace GeometryOfNumbers.Geometry
open Foundation
set_option autoImplicit false

structure IntegerCameraCell where
  base : Nat
  depth : Nat
  core : Nat
  deriving DecidableEq

inductive IntegerCellRole where
  | left | center | right
  deriving DecidableEq

def integerCameraRadius (cell : IntegerCameraCell) : Nat := cell.base ^ cell.depth

def integerCameraCenter (cell : IntegerCameraCell) : Int :=
  (integerCameraRadius cell * cell.core : Nat)

def integerCameraPoint (cell : IntegerCameraCell) : IntegerCellRole → Int
  | .left => leftLeg (integerCameraCenter cell) (integerCameraRadius cell)
  | .center => integerCameraCenter cell
  | .right => rightLeg (integerCameraCenter cell) (integerCameraRadius cell)

/-- Incidence retains the camera address AND the role, even at shared points. -/
def IntegerCameraIncidence (cell : IntegerCameraCell) (role : IntegerCellRole)
    (point : Int) : Prop := integerCameraPoint cell role = point

/-- The core is the tail of the ORIGINAL residual tower, not a quotient chosen
to fit a desired presentation. Depth is still the zero-prefix relation. -/
def integerCameraTowerCell (b n k : Nat) : IntegerCameraCell :=
  ⟨b, k, residualTowerTail (emergentResidualTower b k n)⟩

theorem integerCameraTowerCell_reconstruction (b n k : Nat) (hb : 0 < b)
    (hk : HasCarryDepthAtLeast b n k) :
    integerCameraRadius (integerCameraTowerCell b n k) *
      (integerCameraTowerCell b n k).core = n := by
  have h := hasCarryDepthAtLeast_eq_scaled_tail b n k hb hk
  exact (Nat.mul_comm _ _).trans h.symm

theorem integerCameraTowerCell_center (b n k : Nat) (hb : 0 < b)
    (hk : HasCarryDepthAtLeast b n k) :
    integerCameraCenter (integerCameraTowerCell b n k) = (n : Int) := by
  unfold integerCameraCenter
  rw [integerCameraTowerCell_reconstruction b n k hb hk]

/-- Two presentations reconstruct the same original integer, without
identifying their depths, cores, radii or legs. -/
theorem integerCamera_common_integer (b c n k l : Nat) (hb : 0 < b) (hc : 0 < c)
    (hk : HasCarryDepthAtLeast b n k) (hl : HasCarryDepthAtLeast c n l) :
    IntegerCameraIncidence (integerCameraTowerCell b n k) .center (n : Int) ∧
      IntegerCameraIncidence (integerCameraTowerCell c n l) .center (n : Int) :=
  ⟨integerCameraTowerCell_center b n k hb hk,
    integerCameraTowerCell_center c n l hc hl⟩

theorem integerCamera_point_reflection (cell : IntegerCameraCell) :
    reflect (integerCameraCenter cell) (integerCameraPoint cell .left) =
      integerCameraPoint cell .right :=
  reflect_leftLeg _ _

/-- Exact change of the legs under a change of scale at a fixed center. -/
theorem integerCamera_same_center_leg_displacement (a b : IntegerCameraCell)
    (hc : integerCameraCenter a = integerCameraCenter b) :
    integerCameraPoint a .left - integerCameraPoint b .left =
        (integerCameraRadius b : Int) - integerCameraRadius a ∧
      integerCameraPoint a .right - integerCameraPoint b .right =
        (integerCameraRadius a : Int) - integerCameraRadius b := by
  simp only [integerCameraPoint, leftLeg, rightLeg]
  constructor <;> omega

/-- Distinct positive radii at the same center share precisely that center.
This is incidence compatibility, not a bijection between the two leg pairs. -/
theorem integerCamera_same_center_overlap (a b : IntegerCameraCell)
    (hc : integerCameraCenter a = integerCameraCenter b)
    (ha : 0 < integerCameraRadius a) (hb : 0 < integerCameraRadius b)
    (hab : integerCameraRadius a ≠ integerCameraRadius b)
    (r s : IntegerCellRole) :
    integerCameraPoint a r = integerCameraPoint b s ↔ r = .center ∧ s = .center := by
  cases r <;> cases s <;>
    simp [integerCameraPoint, leftLeg, rightLeg] <;> omega

def integerCamera72Two : IntegerCameraCell := ⟨2, 3, 9⟩
def integerCamera72Three : IntegerCameraCell := ⟨3, 2, 8⟩

theorem integerCamera72_positions :
    (integerCameraPoint integerCamera72Two .left,
      integerCameraPoint integerCamera72Two .center,
      integerCameraPoint integerCamera72Two .right) = (64, 72, 80) ∧
    (integerCameraPoint integerCamera72Three .left,
      integerCameraPoint integerCamera72Three .center,
      integerCameraPoint integerCamera72Three .right) = (63, 72, 81) := by decide

theorem integerCamera72_only_shared_center (r s : IntegerCellRole) :
    integerCameraPoint integerCamera72Two r = integerCameraPoint integerCamera72Three s ↔
      r = .center ∧ s = .center :=
  integerCamera_same_center_overlap _ _ (by decide) (by decide) (by decide) (by decide) r s

end GeometryOfNumbers.Geometry
