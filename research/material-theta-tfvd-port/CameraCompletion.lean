import CompleteTheta
import Mathlib.Analysis.PSeries

/-! Completion of the literal prefix-minus-centres theta port. Camera
amplitude and the logarithmic shear are derived upstream, not tuned. The
critical raw Mellin sum is also tested before any infinite-limit claim. -/
namespace CarryMaterialTheta
open CPFormal.Analytic.Cp NativeCarrySpectralWeyl.Boundary
open scoped BigOperators
noncomputable section
set_option autoImplicit false

def dilationShearLinear (b : ℕ) : MaterialThetaPort →ₗ[ℂ] MaterialThetaPort where
  toFun := dilationShear b
  map_add' p r := by
    ext <;> simp [dilationShear, mul_add]
    ring
  map_smul' a p := by
    ext <;> simp [dilationShear, mul_add]
    ring

def dilatedThetaPort (b : ℕ) (u : ℝ) : MaterialThetaPort :=
  (2 : ℂ) • ∑' n : ℕ, materialThetaMode (b*(n+1)) 1 u

theorem dilated_port_hasSum {b : ℕ} (hb : 0 < b) (u : ℝ) :
    HasSum (fun n : ℕ => materialThetaMode (b*(n+1)) 1 u)
      ((primeCarryAmplitudeRatio b : ℂ) • dilationShearLinear b
        (∑' n : ℕ, materialThetaMode (n+1) 1 (u+Real.log (b : ℝ)))) := by
  have h := ((addressed_port_summable (u+Real.log (b : ℝ))).hasSum.map
    (dilationShearLinear b) (dilationShearLinear b).continuous_of_finiteDimensional).const_smul
      (primeCarryAmplitudeRatio b : ℂ)
  have hf : (fun n : ℕ => materialThetaMode (b*(n+1)) 1 u) =
      fun n : ℕ => (primeCarryAmplitudeRatio b : ℂ) •
        dilationShearLinear b (materialThetaMode (n+1) 1 (u+Real.log (b : ℝ))) := by
    funext n
    exact materialThetaMode_dilation hb (by omega) 1 u
  rw [hf]
  exact h

theorem dilatedThetaPort_eq_shift_shear {b : ℕ} (hb : 0 < b) (u : ℝ) :
    dilatedThetaPort b u =
      (primeCarryAmplitudeRatio b : ℂ) •
        dilationShearLinear b (completedThetaPort (u+Real.log (b : ℝ))) := by
  rw [dilatedThetaPort, (dilated_port_hasSum hb u).tsum_eq, completedThetaPort, map_smul]
  simp only [smul_smul]
  congr 1
  ring

def completedCameraThetaPort (b : ℕ) (u : ℝ) : MaterialThetaPort :=
  completedThetaPort u - (b : ℂ) • dilatedThetaPort b u

theorem completed_camera_shift_formula {b : ℕ} (hb : 0 < b) (u : ℝ) :
    completedCameraThetaPort b u = completedThetaPort u -
      ((b : ℂ)*(primeCarryAmplitudeRatio b : ℂ)) •
        dilationShearLinear b (completedThetaPort (u+Real.log (b : ℝ))) := by
  rw [completedCameraThetaPort, dilatedThetaPort_eq_shift_shear hb, smul_smul]

def dilatedThetaHead (b : ℕ) (T : Finset ℕ) (u : ℝ) : MaterialThetaPort :=
  (2 : ℂ) • ∑ n ∈ T, materialThetaMode (b*(n+1)) 1 u

def dilatedThetaTail (b : ℕ) (T : Finset ℕ) (u : ℝ) : MaterialThetaPort :=
  (2 : ℂ) • ∑' n : {n : ℕ // n ∉ T}, materialThetaMode (b*(n.val+1)) 1 u

theorem dilatedThetaPort_head_tail {b : ℕ} (hb : 0 < b) (T : Finset ℕ) (u : ℝ) :
    dilatedThetaPort b u = dilatedThetaHead b T u + dilatedThetaTail b T u := by
  rw [dilatedThetaPort, dilatedThetaHead, dilatedThetaTail, ← smul_add]
  congr 1
  exact ((dilated_port_hasSum hb u).summable.sum_add_tsum_subtype_compl T).symm

/-- Independent direct-prefix and centre cutoffs, both with their actual
omitted-mode tails. The native odd camera chooses its prescribed cutoffs. -/
theorem completed_camera_head_tail {b : ℕ} (hb : 0 < b)
    (S T : Finset ℕ) (u : ℝ) :
    completedCameraThetaPort b u =
      (thetaPortHead S u - (b : ℂ) • dilatedThetaHead b T u) +
      (thetaPortTail S u - (b : ℂ) • dilatedThetaTail b T u) := by
  rw [completedCameraThetaPort, completedThetaPort_head_tail S u,
    dilatedThetaPort_head_tail hb T u, smul_add]
  abel

def addressTowerPort (b n : ℕ) (a : ℂ) (u : ℝ) (k : ℕ) : MaterialThetaPort :=
  materialThetaMode (b^k*n) a u

theorem address_tower_step {b n : ℕ} (hb : 0 < b) (hn : 0 < n)
    (a : ℂ) (u : ℝ) (k : ℕ) :
    addressTowerPort b n a u (k+1) =
      (primeCarryAmplitudeRatio b : ℂ) •
        dilationShear b (addressTowerPort b n a (u+Real.log (b : ℝ)) k) := by
  unfold addressTowerPort
  rw [pow_succ']
  rw [mul_assoc]
  exact materialThetaMode_dilation hb (mul_pos (pow_pos hb _) hn) a u

/-- A concrete arithmetic-address tower, not an arbitrary moment-built
family, satisfies the existing TFVD with the original Carry amplitude. -/
theorem address_tower_tfvd {b : ℕ} (hb : 0 < b) (n : ℕ)
    (a : ℂ) (u : ℝ) (k : ℕ) :
    addressTowerPort b n a u k =
      portReturn (primeCarryAmplitudeRatio b : ℂ) (addressTowerPort b n a u) k +
      portGreen (primeCarryAmplitudeRatio b : ℂ) (addressTowerPort b n a u) k := by
  apply port_tfvd
  apply Complex.ofReal_ne_zero.mpr
  rw [carry_amplitude_eq_exp hb]
  exact (Real.exp_pos _).ne'

/-- Raw positive material masses do NOT permit swapping the finite Mellin
calibration with the infinite critical sum. Camera cancellation/completion
must be transported first. This is not a no-go for that completed source. -/
theorem raw_critical_material_sum_not_summable :
    ¬ Summable (fun n : ℕ => 1 / (n : ℝ)^(1/2 : ℝ)) := by
  rw [Real.summable_one_div_nat_rpow]
  norm_num

end
end CarryMaterialTheta
