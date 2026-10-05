import GeometryOfNumbers.Analysis.BaseTwoOrdinaryLogGradientCrosswalk
import GeometryOfNumbers.Analysis.C2GlobalPhysicalBranchCanary

/-! # Physical consecutive edges and the existing C2 address chart
The side labels two edges of one complete cell. It is not a depth coordinate.
The endpoint is decoded by the existing odd-material address equivalence.
-/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators lp ENNReal
namespace GeometryOfNumbers.Analysis.BaseTwoCompletion

abbrev BaseTwoPhysicalEdge := ℕ × Fin 2

/-- Side zero is the left edge; side one is the right edge. -/
def baseTwoPhysicalEdgeIndex (e : BaseTwoPhysicalEdge) : ℕ :=
  if e.2.val = 0 then baseTwoCellLeftEdge e.1 else baseTwoCellRightEdge e.1

theorem baseTwoPhysicalEdgeIndex_left (k : ℕ) :
    baseTwoPhysicalEdgeIndex (k, 0) = 4*k+2 := by simp [baseTwoPhysicalEdgeIndex]

theorem baseTwoPhysicalEdgeIndex_right (k : ℕ) :
    baseTwoPhysicalEdgeIndex (k, 1) = 4*k+3 := by simp [baseTwoPhysicalEdgeIndex]

theorem baseTwoPhysicalEdgeIndex_injective : Function.Injective baseTwoPhysicalEdgeIndex := by
  rintro ⟨k,a⟩ ⟨l,b⟩ h
  have ha := a.isLt
  have hb := b.isLt
  simp only [baseTwoPhysicalEdgeIndex, baseTwoCellLeftEdge_eq,
    baseTwoCellRightEdge_eq] at h
  change (if a.val = 0 then 4*k+2 else 4*k+3) =
    (if b.val = 0 then 4*l+2 else 4*l+3) at h
  split at h <;> split at h <;>
    apply Prod.ext <;> first | (change k = l; omega) |
      (apply Fin.ext; change a.val = b.val; omega)

theorem baseTwoPhysicalEdgeIndex_range (n : ℕ) :
    n ∈ Set.range baseTwoPhysicalEdgeIndex ↔ n % 4 = 2 ∨ n % 4 = 3 := by
  constructor
  · rintro ⟨⟨k,a⟩,rfl⟩
    fin_cases a <;> simp [baseTwoPhysicalEdgeIndex, Nat.add_mod]
  · intro h
    rcases h with h | h
    · exact ⟨(n/4,0), by rw [baseTwoPhysicalEdgeIndex_left]; omega⟩
    · exact ⟨(n/4,1), by rw [baseTwoPhysicalEdgeIndex_right]; omega⟩

/-- The odd endpoint of the same cell edge, before any address decoding. -/
def baseTwoPhysicalEdgeOddEndpoint (e : BaseTwoPhysicalEdge) : OddMaterialIndex :=
  ⟨⟨if e.2.val = 0 then 4*e.1+3 else 4*e.1+5, by
      split <;> omega⟩,
   by
     change Odd (if e.2.val = 0 then 4*e.1+3 else 4*e.1+5)
     rw [Nat.odd_iff]
     split <;> omega,
   by
     change 3 ≤ (if e.2.val = 0 then 4*e.1+3 else 4*e.1+5)
     split <;> omega⟩

theorem baseTwoPhysicalEdgeOddEndpoint_left (k : ℕ) :
    ((baseTwoPhysicalEdgeOddEndpoint (k,0)).val : ℕ) = 4*k+3 := rfl

theorem baseTwoPhysicalEdgeOddEndpoint_right (k : ℕ) :
    ((baseTwoPhysicalEdgeOddEndpoint (k,1)).val : ℕ) = 4*k+5 := rfl

/-- Arithmetic inverse; no choice selects an edge. -/
def oddMaterialPhysicalEdge (n : OddMaterialIndex) : BaseTwoPhysicalEdge :=
  if (n.val : ℕ) % 4 = 3 then (((n.val : ℕ)-3)/4, 0)
    else (((n.val : ℕ)-5)/4, 1)

theorem oddMaterialPhysicalEdge_endpoint (e : BaseTwoPhysicalEdge) :
    oddMaterialPhysicalEdge (baseTwoPhysicalEdgeOddEndpoint e) = e := by
  rcases e with ⟨k,a⟩
  fin_cases a <;>
    simp [oddMaterialPhysicalEdge, baseTwoPhysicalEdgeOddEndpoint,
      Nat.add_mod]

theorem baseTwoPhysicalEdgeOddEndpoint_decode (n : OddMaterialIndex) :
    baseTwoPhysicalEdgeOddEndpoint (oddMaterialPhysicalEdge n) = n := by
  apply Subtype.ext
  apply PNat.eq
  have ho := Nat.odd_iff.mp n.property.1
  have hg := n.property.2
  unfold oddMaterialPhysicalEdge baseTwoPhysicalEdgeOddEndpoint
  split <;> norm_num at * <;> omega

def baseTwoPhysicalEdgeEquivOddMaterial : BaseTwoPhysicalEdge ≃ OddMaterialIndex where
  toFun := baseTwoPhysicalEdgeOddEndpoint
  invFun := oddMaterialPhysicalEdge
  left_inv := oddMaterialPhysicalEdge_endpoint
  right_inv := baseTwoPhysicalEdgeOddEndpoint_decode

/-- Existing material decoding supplies core, direction and true depth. -/
def baseTwoPhysicalEdgeEquivC2Address : BaseTwoPhysicalEdge ≃ GlobalC2BranchAddress :=
  baseTwoPhysicalEdgeEquivOddMaterial.trans globalC2BranchAddressEquivOddMaterial.symm

def baseTwoPhysicalEdgeC2Address (e : BaseTwoPhysicalEdge) : GlobalC2BranchAddress :=
  baseTwoPhysicalEdgeEquivC2Address e

theorem baseTwoPhysicalEdgeC2Address_eq (e : BaseTwoPhysicalEdge) :
    baseTwoPhysicalEdgeC2Address e = oddMaterialC2Address (baseTwoPhysicalEdgeOddEndpoint e) := rfl

theorem baseTwoPhysicalEdgeC2Address_material (e : BaseTwoPhysicalEdge) :
    globalC2MaterialAddress (baseTwoPhysicalEdgeC2Address e) =
      (baseTwoPhysicalEdgeOddEndpoint e).val :=
  globalC2MaterialAddress_decode _

/-- The existing C2 neighbor is exactly the original base-two cell center. -/
theorem baseTwoPhysicalEdgeOddEndpoint_neighbor (e : BaseTwoPhysicalEdge) :
    oddMaterialNeighborCenter (baseTwoPhysicalEdgeOddEndpoint e) = baseTwoCenter e.1 := by
  rcases e with ⟨k,a⟩
  fin_cases a <;>
    simp [oddMaterialNeighborCenter, baseTwoPhysicalEdgeOddEndpoint,
      Nat.add_mod, baseTwo_center_eq] <;> omega

theorem baseTwoPhysicalEdgeC2Address_direction (e : BaseTwoPhysicalEdge) :
    (baseTwoPhysicalEdgeC2Address e).2.1 = e.2 := by
  rw [baseTwoPhysicalEdgeC2Address_eq, oddMaterialC2Address_sign]
  rcases e with ⟨k,a⟩
  fin_cases a <;> simp [baseTwoPhysicalEdgeOddEndpoint, Nat.add_mod]

theorem baseTwoPhysicalEdgeC2Address_depth (e : BaseTwoPhysicalEdge) :
    c2BranchDepth (baseTwoPhysicalEdgeC2Address e).2 = (baseTwoCenter e.1).factorization 2 := by
  rw [baseTwoPhysicalEdgeC2Address_eq, oddMaterialC2Address_depth,
    baseTwoPhysicalEdgeOddEndpoint_neighbor]

theorem baseTwoPhysicalEdgeC2Address_center (e : BaseTwoPhysicalEdge) :
    2 ^ c2BranchDepth (baseTwoPhysicalEdgeC2Address e).2 *
      (baseTwoPhysicalEdgeC2Address e).1.val = baseTwoCenter e.1 := by
  rw [baseTwoPhysicalEdgeC2Address_eq, oddMaterialC2Address_depth]
  have h := Nat.ordProj_mul_ordCompl_eq_self
    (oddMaterialNeighborCenter (baseTwoPhysicalEdgeOddEndpoint e)) 2
  change 2 ^ (oddMaterialNeighborCenter (baseTwoPhysicalEdgeOddEndpoint e)).factorization 2 *
    (oddMaterialC2Address (baseTwoPhysicalEdgeOddEndpoint e)).1.val =
    oddMaterialNeighborCenter (baseTwoPhysicalEdgeOddEndpoint e) at h
  exact h.trans (baseTwoPhysicalEdgeOddEndpoint_neighbor e)

/-- Endpoint incidence has the original center-minus/plus-one orientation. -/
theorem baseTwoPhysicalEdgeOddEndpoint_incidence (e : BaseTwoPhysicalEdge) :
    ((baseTwoPhysicalEdgeOddEndpoint e).val : ℕ) =
      if e.2.val = 0 then baseTwoCenter e.1 - 1 else baseTwoCenter e.1 + 1 := by
  rcases e with ⟨k,a⟩
  fin_cases a <;> simp [baseTwoPhysicalEdgeOddEndpoint, baseTwo_center_eq] <;> omega

end GeometryOfNumbers.Analysis.BaseTwoCompletion
