import BoundaryTransport
import CorrelationInterval

namespace C3CofactorCorrelation

open CarryC3Boxes CarryC3Tail CarryC3Gamma C3Cofactor
open scoped BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 30000

/-- Exact rational enclosures for the finite C3/48 reference coefficients.
The tables are obtained by outward-rounded rational interval operations; the
following subset theorem rechecks every endpoint in Lean. -/
def nativeEvenFiniteReferenceBoxTable : Fin 7 → Box := ![
  ⟨497120778188314109911949 / 1000000000000000000000000,
    248560389094157054956699 / 500000000000000000000000⟩,
  ⟨-11485972157572718772029 / 1000000000000000000000000,
    -11485972157572718763297 / 1000000000000000000000000⟩,
  ⟨123452018070317998837 / 1000000000000000000000000,
    123452018070318015143 / 1000000000000000000000000⟩,
  ⟨-83235548138553433 / 100000000000000000000000,
    -104044435173190009 / 125000000000000000000000⟩,
  ⟨998056637835073 / 250000000000000000000000,
    3992226551348241 / 1000000000000000000000000⟩,
  ⟨-7308012881523 / 500000000000000000000000,
    -14616025757709 / 1000000000000000000000000⟩,
  ⟨42745395487 / 1000000000000000000000000,
    213727037 / 5000000000000000000000⟩
]

theorem native_even_finite_reference_box_subset_table (j : Fin 7) :
    (nativeEvenFiniteReferenceBox j).Subset
      (nativeEvenFiniteReferenceBoxTable j) := by
  fin_cases j <;> decide +kernel

theorem native_even_finite_reference_candidate_margin (j : Fin 7) :
    ((candidateCoefficientBall j).center : ℝ) -
        (((candidateCoefficientBall j).radius - 3/10^24 : ℚ) : ℝ) ≤
      (nativeEvenFiniteReferenceBoxTable j).lo ∧
    (nativeEvenFiniteReferenceBoxTable j).hi ≤
      ((candidateCoefficientBall j).center : ℝ) +
        (((candidateCoefficientBall j).radius - 3/10^24 : ℚ) : ℝ) := by
  fin_cases j <;>
    norm_num [nativeEvenFiniteReferenceBoxTable, candidateCoefficientBall]

theorem native_even_coefficient_candidate_contains (j : Fin 7) :
    (candidateCoefficientBall j).Contains (nativeC j.val) := by
  change |nativeC j.val - (candidateCoefficientBall j).center| ≤
    (candidateCoefficientBall j).radius
  have hfinite := Box.subset_contains
    (native_even_finite_reference_box_subset_table j)
    (native_even_finite_reference_box_contains j)
  have hmarg := native_even_finite_reference_candidate_margin j
  have hlo : ((candidateCoefficientBall j).center : ℝ) -
      (((candidateCoefficientBall j).radius - 3/10^24 : ℚ) : ℝ) ≤
        (nativeEvenFiniteReferenceBoxTable j).lo := hmarg.1
  have hhi : (nativeEvenFiniteReferenceBoxTable j).hi ≤
      ((candidateCoefficientBall j).center : ℝ) +
        (((candidateCoefficientBall j).radius - 3/10^24 : ℚ) : ℝ) := hmarg.2
  let x : ℝ := (-1:ℝ)^j.val *
    finiteCompletedRealJet48 ⟨2*j.val, by omega⟩
  have hxl : ((candidateCoefficientBall j).center : ℝ) -
      (((candidateCoefficientBall j).radius - 3/10^24 : ℚ) : ℝ) ≤ x :=
    le_trans hlo hfinite.1
  have hxu : x ≤ ((candidateCoefficientBall j).center : ℝ) +
      (((candidateCoefficientBall j).radius - 3/10^24 : ℚ) : ℝ) :=
    le_trans hfinite.2 hhi
  have hx : |x - (candidateCoefficientBall j).center| ≤
      ((candidateCoefficientBall j).radius - 3/10^24 : ℚ) := by
    rw [abs_le]
    constructor <;> linarith
  have he := native_even_coefficient_finite_reference_error j
  have htriangle : |nativeC j.val - (candidateCoefficientBall j).center| ≤
      |nativeC j.val - x| + |x - (candidateCoefficientBall j).center| := by
    calc
      |nativeC j.val - (candidateCoefficientBall j).center| =
          |(nativeC j.val - x) + (x - (candidateCoefficientBall j).center)| := by
            congr 1; ring
      _ ≤ |nativeC j.val - x| + |x - (candidateCoefficientBall j).center| :=
        abs_add_le _ _
  have he' : |nativeC j.val - x| ≤ (3/10^24:ℝ) := by
    simpa [x] using he
  have hx' : |x - (candidateCoefficientBall j).center| ≤
      (candidateCoefficientBall j).radius - 3/10^24 := by
    have hcast : (((candidateCoefficientBall j).radius - 3/10^24 : ℚ) : ℝ) =
        ((candidateCoefficientBall j).radius : ℝ) - (3/10^24:ℝ) := by
      push_cast
      norm_num
    rw [hcast] at hx
    exact hx
  linarith

theorem native_even_source_coefficient_boxes :
    ∀ j : Fin 7, (candidateCoefficientBall j).Contains (nativeC j.val) :=
  native_even_coefficient_candidate_contains

end
end C3CofactorCorrelation
