import CarrySelfAdjointOperator.NativeCauchyLaguerreSources

/-! Test an inherited conservative map on the SAME physical Cauchy carrier.
The complement is the old Laguerre head, never a target moment Gram. -/
namespace CarryConservativeIntertwiner
open CarrySelfAdjointOperator CarrySelfAdjointOperator.NativeLaguerre
open scoped InnerProductSpace ComplexConjugate BigOperators lp ENNReal
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- Negative sign is the original central return orientation q(0)=-1. -/
def conservativeReturn (R : ℕ) : PhysicalCauchySpace →L[ℂ] PhysicalCauchySpace :=
  -physicalCauchyShift (R+1)

def conservativeHead (R : ℕ) (x : PhysicalCauchySpace) : ℓ²(ℕ,ℂ) :=
  laguerreHead R (cauchyLaguerreIsometry x)

theorem conservative_pairing (R : ℕ) (x y : PhysicalCauchySpace) :
    inner ℂ x y = inner ℂ (conservativeHead R x) (conservativeHead R y)+
      inner ℂ (conservativeReturn R x) (conservativeReturn R y) := by
  simpa only [conservativeHead,conservativeReturn,neg_apply,
    inner_neg_left,inner_neg_right,neg_neg] using physicalCauchy_head_tail_inner R x y

theorem conservative_energy (R : ℕ) (x : PhysicalCauchySpace) :
    ‖x‖^2-‖conservativeReturn R x‖^2=‖conservativeHead R x‖^2 := by
  have h := physicalCauchy_head_tail_energy R x
  simpa only [conservativeReturn,neg_apply,norm_neg,conservativeHead]
    using (sub_eq_iff_eq_add.mpr h.symm)

/-- Exact failure of the candidate transport, with both actual channels supplied. -/
def transportDefect (R : ℕ) (incident returned : PhysicalCauchySpace) : PhysicalCauchySpace :=
  returned-conservativeReturn R incident

/-- Two independent source pairs. All three error crosses are retained. -/
theorem polarized_defect_ledger (R : ℕ) (x rx y ry : PhysicalCauchySpace) :
    inner ℂ x y-inner ℂ rx ry =
      inner ℂ (conservativeHead R x) (conservativeHead R y)-
      inner ℂ (conservativeReturn R x) (transportDefect R y ry)-
      inner ℂ (transportDefect R x rx) (conservativeReturn R y)-
      inner ℂ (transportDefect R x rx) (transportDefect R y ry) := by
  have h := conservative_pairing R x y
  unfold transportDefect
  simp only [inner_sub_left,inner_sub_right]
  linear_combination h

theorem energy_defect_ledger (R : ℕ) (x rx : PhysicalCauchySpace) :
    ‖x‖^2-‖rx‖^2=‖conservativeHead R x‖^2-
      2*(inner ℂ (conservativeReturn R x) (transportDefect R x rx)).re-
      ‖transportDefect R x rx‖^2 := by
  have h := congrArg Complex.re (polarized_defect_ledger R x rx x rx)
  simp only [Complex.sub_re] at h
  have hs (z : PhysicalCauchySpace) : (inner ℂ z z).re=‖z‖^2 :=
    (norm_sq_eq_re_inner (𝕜:=ℂ) z).symm
  have hh (z : ℓ²(ℕ,ℂ)) : (inner ℂ z z).re=‖z‖^2 :=
    (norm_sq_eq_re_inner (𝕜:=ℂ) z).symm
  rw [hs x,hs rx,hh _,hs _] at h
  have he := congrArg Complex.re (inner_conj_symm (conservativeReturn R x) (transportDefect R x rx))
  simp only [Complex.conj_re] at he
  linarith

end
end CarryConservativeIntertwiner
