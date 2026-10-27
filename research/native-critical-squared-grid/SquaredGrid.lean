import AllOrderGreenFilters

namespace CarryCriticalGrid
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryCommutatorControl CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryMixedParity CarryCrossRadial CarryGreenLeading CarryGreenCubic CarryOddGreen CarryCubicOdd CarryCurvatureGreen CarryOddCauchy NativeLaguerre NativeCauchyPorts
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4800000

/-- Only a change of coordinates on FOUR readout samples, not a physical clock. -/
def squaredNode (e : ℂ) (j : Fin 4) : ℂ := e*((j:ℂ)+1)^2

def gridFirst (e : ℂ) (f : Fin 4 → ℂ) : ℂ := (f 1-f 0)/(3*e)
def gridSecond (e : ℂ) (f : Fin 4 → ℂ) : ℂ :=
  ((f 2-f 1)/(5*e)-(f 1-f 0)/(3*e))/(8*e)
def gridSecondRight (e : ℂ) (f : Fin 4 → ℂ) : ℂ :=
  ((f 3-f 2)/(7*e)-(f 2-f 1)/(5*e))/(12*e)
def gridThird (e : ℂ) (f : Fin 4 → ℂ) : ℂ :=
  (gridSecondRight e f-gridSecond e f)/(15*e)

/-- The third divided difference with all four squared-address nodes. -/
theorem grid_third_barycentric (e : ℂ) (he : e≠0) (f : Fin 4 → ℂ) :
    gridThird e f= -f 0/(360*e^3)+f 1/(180*e^3)-f 2/(280*e^3)+f 3/(1260*e^3) := by
  unfold gridThird gridSecondRight gridSecond
  field_simp
  ring

/-- Value + initial slope + the two remaining Newton data recover EVERY sample.
This is a lossless scalar coordinate change AFTER physical synthesis. -/
theorem squared_grid_reconstruction (e : ℂ) (he : e≠0) (f : Fin 4 → ℂ) (j : Fin 4) :
    f j=f 0+(squaredNode e j-e)*gridFirst e f+
      (squaredNode e j-e)*(squaredNode e j-4*e)*gridSecond e f+
      (squaredNode e j-e)*(squaredNode e j-4*e)*(squaredNode e j-9*e)*gridThird e f := by
  have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by fin_cases j <;> decide
  rcases hj with rfl | rfl | rfl | rfl
  all_goals norm_num [squaredNode,gridFirst,gridSecond,gridThird,gridSecondRight]
  all_goals field_simp
  all_goals ring

theorem squared_grid_data_injective (e : ℂ) (he : e≠0) :
    Function.Injective (fun f : Fin 4 → ℂ => (f 0,gridFirst e f,gridSecond e f,gridThird e f)) := by
  intro f g hfg
  have h0 : f 0=g 0 := congrArg (fun t : ℂ × ℂ × ℂ × ℂ => t.1) hfg
  have h1 : gridFirst e f=gridFirst e g := congrArg (fun t : ℂ × ℂ × ℂ × ℂ => t.2.1) hfg
  have h2 : gridSecond e f=gridSecond e g := congrArg (fun t : ℂ × ℂ × ℂ × ℂ => t.2.2.1) hfg
  have h3 : gridThird e f=gridThird e g := congrArg (fun t : ℂ × ℂ × ℂ × ℂ => t.2.2.2) hfg
  funext j
  rw [squared_grid_reconstruction e he f j,squared_grid_reconstruction e he g j]
  rw [h0,h1,h2,h3]

/-- Multiplication by the squared material coordinate keeps its endpoint term. -/
theorem grid_third_mul_node (e : ℂ) (he : e≠0) (f : Fin 4 → ℂ) :
    gridThird e (fun j => squaredNode e j*f j)=gridSecond e f+16*e*gridThird e f := by
  unfold gridThird gridSecondRight gridSecond
  norm_num [squaredNode]
  field_simp
  ring

/-- The top TWO nodal factors cancel to the original lower-order slope. -/
theorem grid_third_top_factors (e : ℂ) (he : e≠0) (f : Fin 4 → ℂ) :
    gridThird e (fun j => (squaredNode e j-9*e)*(squaredNode e j-16*e)*f j)=gridFirst e f := by
  unfold gridThird gridSecondRight gridSecond gridFirst
  norm_num [squaredNode]
  field_simp
  ring

/-- The constant normalized source term cancels, without discarding its state. -/
theorem grid_constant_cancellation (e c : ℂ) :
    gridFirst e (fun _ => c)=0 ∧ gridSecond e (fun _ => c)=0 ∧ gridThird e (fun _ => c)=0 := by
  simp [gridFirst,gridSecond,gridThird,gridSecondRight]

end
end CarryCriticalGrid
