import MellinAtlas

/-! The actual infinite theta source is synthesized with its addressed
material-log channel and theta derivative. Tails are sums of the ORIGINAL
omitted modes, not independently chosen scalar remainders. -/
namespace CarryMaterialTheta
open CarrySelfAdjointOperator XiThetaCosine NativeCarrySpectralWeyl.Boundary
open scoped BigOperators
noncomputable section
set_option autoImplicit false

theorem summable_square_address_mode (u : ℝ) :
    Summable (fun n : ℕ => ((n+1 : ℕ) : ℝ)^2 * thetaTailMode n u) := by
  have h := (((summable_thetaTailMode u).mul_left (1/2 : ℝ)).sub
    (summable_thetaTailModeFirst u)).div_const (2*Real.pi*Real.exp (2*u))
  apply h.congr
  intro n
  simp only [thetaTailModeFirst]
  field_simp
  ring

theorem summable_material_log_mode (u : ℝ) :
    Summable (fun n : ℕ => Real.log ((n+1 : ℕ) : ℝ)*thetaTailMode n u) := by
  apply Summable.of_norm_bounded (summable_square_address_mode u)
  intro n
  have hn : 0 < ((n+1 : ℕ) : ℝ) := by positivity
  have hlog : 0 ≤ Real.log ((n+1 : ℕ) : ℝ) := Real.log_nonneg (by norm_cast; omega)
  have hmode : 0 < thetaTailMode n u := addressMode_pos (n+1) u
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hlog hmode.le)]
  apply mul_le_mul_of_nonneg_right _ hmode.le
  have h := Real.log_le_sub_one_of_pos hn
  nlinarith [sq_nonneg (((n+1 : ℕ) : ℝ)-1)]

theorem addressed_port_hasSum (u : ℝ) :
    HasSum (fun n : ℕ => materialThetaMode (n+1) 1 u)
      (((∑' n : ℕ, thetaTailMode n u : ℝ) : ℂ),
       ((((∑' n : ℕ, Real.log ((n+1 : ℕ) : ℝ)*thetaTailMode n u : ℝ) : ℂ)),
        ((∑' n : ℕ, thetaTailModeFirst n u : ℝ) : ℂ))) := by
  have hv := Complex.hasSum_ofReal.mpr (summable_thetaTailMode u).hasSum
  have hl := Complex.hasSum_ofReal.mpr (summable_material_log_mode u).hasSum
  have hd := Complex.hasSum_ofReal.mpr (summable_thetaTailModeFirst u).hasSum
  simpa only [materialThetaMode, one_mul, addressMode_succ, addressModeFirst_succ] using
    hv.prodMk (hl.prodMk hd)

theorem addressed_port_summable (u : ℝ) :
    Summable (fun n : ℕ => materialThetaMode (n+1) 1 u) :=
  (addressed_port_hasSum u).summable

def completedThetaPort (u : ℝ) : MaterialThetaPort :=
  (2 : ℂ) • ∑' n : ℕ, materialThetaMode (n+1) 1 u

theorem completedThetaPort_components (u : ℝ) :
    completedThetaPort u =
      ((thetaTail u : ℂ),
       (((2 * ∑' n : ℕ, Real.log ((n+1 : ℕ) : ℝ)*thetaTailMode n u : ℝ) : ℂ),
        (thetaTailFirst u : ℂ))) := by
  rw [completedThetaPort, (addressed_port_hasSum u).tsum_eq,
    thetaTail_eq_two_mul_tsum]
  simp only [Prod.smul_mk, smul_eq_mul, Complex.ofReal_mul, thetaTailFirst,
    Complex.ofReal_ofNat]

def thetaPortHead (S : Finset ℕ) (u : ℝ) : MaterialThetaPort :=
  (2 : ℂ) • ∑ n ∈ S, materialThetaMode (n+1) 1 u

def thetaPortTail (S : Finset ℕ) (u : ℝ) : MaterialThetaPort :=
  (2 : ℂ) • ∑' n : {n : ℕ // n ∉ S}, materialThetaMode (n.val+1) 1 u

/-- Exact vector synthesis including the infinite omitted-address tail. -/
theorem completedThetaPort_head_tail (S : Finset ℕ) (u : ℝ) :
    completedThetaPort u = thetaPortHead S u + thetaPortTail S u := by
  rw [completedThetaPort, thetaPortHead, thetaPortTail, ← smul_add]
  congr 1
  exact ((addressed_port_summable u).sum_add_tsum_subtype_compl S).symm

def logPortLinear : MaterialThetaPort →ₗ[ℂ] (ℂ × ℂ) where
  toFun := logPort
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def derivativePortLinear : MaterialThetaPort →ₗ[ℂ] (ℂ × ℂ) where
  toFun := derivativePort
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Both Green projections retain HH, HT, TH, TT for independent cutoffs
and independent theta parameters. No tail or crossing is set to zero. -/
theorem completed_theta_green_four_crosses
    (π : MaterialThetaPort →ₗ[ℂ] (ℂ × ℂ))
    (S T : Finset ℕ) (u v : ℝ) :
    greenForm (𝕜 := ℂ) (π (completedThetaPort u)) (π (completedThetaPort v)) =
      greenForm (𝕜 := ℂ) (π (thetaPortHead S u)) (π (thetaPortHead T v)) +
      greenForm (𝕜 := ℂ) (π (thetaPortHead S u)) (π (thetaPortTail T v)) +
      greenForm (𝕜 := ℂ) (π (thetaPortTail S u)) (π (thetaPortHead T v)) +
      greenForm (𝕜 := ℂ) (π (thetaPortTail S u)) (π (thetaPortTail T v)) := by
  rw [completedThetaPort_head_tail S u, completedThetaPort_head_tail T v,
    map_add, map_add, greenForm_add_left, greenForm_add_right, greenForm_add_right]
  ring

end
end CarryMaterialTheta
