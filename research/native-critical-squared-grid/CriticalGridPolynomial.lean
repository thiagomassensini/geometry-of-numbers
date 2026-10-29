import SquaredGrid

namespace CarryCriticalGrid
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryCommutatorControl CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryMixedParity CarryCrossRadial CarryGreenLeading CarryGreenCubic CarryOddGreen CarryCubicOdd CarryCurvatureGreen CarryOddCauchy NativeLaguerre NativeCauchyPorts
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4800000

/-- The polynomial induced by the ORIGINAL critical coefficients on this mesh.
It is not an adjusted source, moment sequence or metric. -/
def criticalGridPolynomial (e a b u : ℂ) : ℂ :=
  1+(a+b)*(u+12*e)+a*b*(u-9*e)*(u-16*e)

/-- Exact finite-grid defect from the coalescing-node product. -/
theorem critical_polynomial_limit_product (e a b u : ℂ) :
    criticalGridPolynomial e a b u=(1+a*u)*(1+b*u)+
      e*(12*(a+b)-25*a*b*u)+144*a*b*e^2 := by
  unfold criticalGridPolynomial
  ring

/-- The 49 e u correction survives polarization, with independent a,b. -/
theorem critical_polynomial_shifted_product (e a b u : ℂ) :
    criticalGridPolynomial e a b u=(1+a*(u+12*e))*(1+b*(u+12*e))-49*a*b*e*u := by
  unfold criticalGridPolynomial
  ring

/-- A readout of the COMPLETE signed balance, after synthesis. -/
def gridBalance (e a b : ℂ) (f : Fin 4 → ℂ) : ℂ :=
  -gridThird e (fun j => criticalGridPolynomial e a b (squaredNode e j)*f j)

/-- Three independent finite curvatures; the mixed endpoint correction is kept. -/
theorem critical_grid_curvatures (e : ℂ) (he : e≠0) (a b : ℂ) (f : Fin 4 → ℂ) :
    gridBalance e a b f= -gridThird e f-
      (a+b)*(gridSecond e f+28*e*gridThird e f)-a*b*gridFirst e f := by
  unfold gridBalance criticalGridPolynomial gridThird gridSecondRight gridSecond gridFirst
  norm_num [squaredNode]
  field_simp
  ring

/-- Recover the mixed curvature from TWO independent trial inputs. -/
theorem grid_mixed_from_pairs (e : ℂ) (he : e≠0) (f : Fin 4 → ℂ) :
    gridSecond e f+28*e*gridThird e f=gridBalance e 0 0 f-gridBalance e 1 0 f := by
  rw [critical_grid_curvatures e he,critical_grid_curvatures e he]
  ring

/-- Polarized finite difference of the trial coefficients recovers the first slope. -/
theorem grid_first_from_pairs (e : ℂ) (he : e≠0) (f : Fin 4 → ℂ) :
    gridFirst e f= -gridBalance e 1 1 f+gridBalance e 1 0 f+
      gridBalance e 0 1 f-gridBalance e 0 0 f := by
  rw [critical_grid_curvatures e he,critical_grid_curvatures e he,
    critical_grid_curvatures e he,critical_grid_curvatures e he]
  ring

/-- Constant normalized response has exactly zero readout, for BOTH inputs. -/
theorem critical_grid_constant (e : ℂ) (he : e≠0) (a b c : ℂ) :
    gridBalance e a b (fun _ => c)=0 := by
  rw [critical_grid_curvatures e he]
  simp [gridFirst,gridSecond,gridThird,gridSecondRight]

/-- Finite-grid product minus its EXPLICIT defect; no positivity is inferred. -/
theorem critical_grid_product_defect (e a b : ℂ) (f : Fin 4 → ℂ) :
    gridBalance e a b f=
      -gridThird e (fun j => (1+a*(squaredNode e j+12*e))*(1+b*(squaredNode e j+12*e))*f j)+
      49*a*b*e*gridThird e (fun j => squaredNode e j*f j) := by
  unfold gridBalance
  simp_rw [critical_polynomial_shifted_product]
  unfold gridThird gridSecondRight gridSecond
  ring

end
end CarryCriticalGrid
