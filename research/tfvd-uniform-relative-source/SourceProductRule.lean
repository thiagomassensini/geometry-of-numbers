import SourceBezout

namespace CarrySourceBezout
open scoped BigOperators
noncomputable section

variable {R : Type*} [CommRing R] [IsDomain R]

/-- Sector-specific source operator used in the original source kernel. -/
def sourceOperator (oddSector : Bool) (C : PowerSeries R) : PowerSeries R :=
  let A := -(PowerSeries.derivative R C)
  if oddSector then A else PowerSeries.X * A

/-- Same Bézout construction as `sourceKernel`, now directly on a formal series. -/
def sourceKernelSeries (oddSector : Bool) (C : PowerSeries R) : BiSeries R :=
  bezout (sourceOperator oddSector C) C

omit [IsDomain R] in
theorem sourceOperator_mul (oddSector : Bool) (H U : PowerSeries R) :
    sourceOperator oddSector (H * U) =
      U * sourceOperator oddSector H + H * sourceOperator oddSector U := by
  have hbase :
      -(PowerSeries.derivative R (H * U)) =
        U * (-(PowerSeries.derivative R H)) + H * (-(PowerSeries.derivative R U)) := by
    calc
      -(PowerSeries.derivative R (H * U))
          = -(H * PowerSeries.derivative R U + U * PowerSeries.derivative R H) := by
            exact congrArg Neg.neg ((PowerSeries.derivative R).leibniz H U)
      _ = U * (-(PowerSeries.derivative R H)) + H * (-(PowerSeries.derivative R U)) := by
            ring
  cases oddSector with
  | true =>
      dsimp [sourceOperator]
      exact hbase
  | false =>
      calc
        sourceOperator false (H * U)
            = PowerSeries.X * (-(PowerSeries.derivative R (H * U))) := by
                simp [sourceOperator]
        _ = PowerSeries.X *
            (U * (-(PowerSeries.derivative R H)) + H * (-(PowerSeries.derivative R U))) := by
              rw [hbase]
        _ = U * sourceOperator false H + H * sourceOperator false U := by
              simp [sourceOperator]
              ring

/-- Algebraic scaling rule under a common multiplicative factor. -/
theorem bezout_mul_common (U A C : PowerSeries R) :
    bezout (U * A) (U * C) = left U * right U * bezout A C := by
  apply mul_left_cancel₀ uv_ne_zero
  rw [bezout_numerator]
  conv_rhs =>
    rw [show uv * (left U * right U * bezout A C) =
      left U * right U * (uv * bezout A C) by ring]
  conv_rhs => rw [bezout_numerator]
  simp [map_mul]
  ring

/-- Exact multiplicative product rule for the source Bézout kernel, both sectors. -/
theorem sourceKernelSeries_product_rule (oddSector : Bool) (H U : PowerSeries R) :
    sourceKernelSeries oddSector (H * U) =
      left U * right U * sourceKernelSeries oddSector H +
      left H * right H * sourceKernelSeries oddSector U := by
  unfold sourceKernelSeries
  rw [sourceOperator_mul, bezout_add_left]
  have hU :
      bezout (U * sourceOperator oddSector H) (H * U) =
        left U * right U * bezout (sourceOperator oddSector H) H := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      (bezout_mul_common U (sourceOperator oddSector H) H)
  have hH :
      bezout (H * sourceOperator oddSector U) (H * U) =
        left H * right H * bezout (sourceOperator oddSector U) U := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      (bezout_mul_common H (sourceOperator oddSector U) U)
  rw [hU, hH]

/-- Finite-block consequence of the product rule at the coefficient-block level. -/
theorem coefficientBlock_sourceKernelSeries_product_rule
    (oddSector : Bool) (H U : PowerSeries R) (r : ℕ) :
    coefficientBlock (sourceKernelSeries oddSector (H * U)) r =
      coefficientBlock (left U * right U * sourceKernelSeries oddSector H) r +
      coefficientBlock (left H * right H * sourceKernelSeries oddSector U) r := by
  rw [sourceKernelSeries_product_rule]
  ext i j
  simp [coefficientBlock]

end
end CarrySourceBezout
