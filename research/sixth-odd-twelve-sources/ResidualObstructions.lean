import OddOrderedCertificate

/-! Source-backed obstruction to uniform raw-coordinate conditioning, plus
finite counterexamples to insufficient positivity proxies. These statements
do not assert failure of any future source-derived residual certificate. -/
namespace CarryResidualObstructions
open CarrySelfAdjointOperator CarryCriticalSource CarryVariationalSchur
open scoped BigOperators Matrix Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000

/-- A coercivity constant is bounded by EVERY actual diagonal entry. -/
theorem source_coercivity_le_last_diagonal (m : ℕ → ℝ) (s n : ℕ) (α : ℝ)
    (hcoerc : ∀ y : Fin (n+1) → ℝ,
      α*(y ⬝ᵥ y) ≤ sourceMomentQuadratic m s (n+1) y) :
    α ≤ m (2*n+s) := by
  have hb := hcoerc (Pi.single (Fin.last n) 1)
  simpa [sourceMomentQuadratic,sourceMomentMatrix,single_dotProduct,Matrix.mulVec_single,
    show n+n+s=2*n+s by omega] using hb

/-- A necessary order-dependent bound from the existing UNCONDITIONAL
source decay, without assuming any next pivot positive. -/
theorem native_coercivity_upper_bound (s n : ℕ) (α : ℝ)
    (hcoerc : ∀ y : Fin (n+1) → ℝ,
      α*(y ⬝ᵥ y) ≤ sourceMomentQuadratic h s (n+1) y) :
    α ≤ (22/175:ℝ)^(n+1) := by
  calc
    α ≤ h (2*n+s) := source_coercivity_le_last_diagonal h s n α hcoerc
    _ ≤ |h (2*n+s)| := le_abs_self _
    _ ≤ (22/175:ℝ)^(2*n+s+1)-(1/25:ℝ)^(2*n+s+1) :=
      canonicalCompletedNativeLogDerivativeMoment_sharp_decay (2*n+s)
    _ ≤ (22/175:ℝ)^(2*n+s+1) := sub_le_self _ (by positivity)
    _ ≤ (22/175:ℝ)^(n+1) := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)

/-- Uniform positive coercivity in these unscaled moment coordinates is
impossible even if every finite block is eventually proved positive. -/
theorem no_uniform_native_coercivity (s : ℕ) :
    ¬ ∃ α : ℝ, 0 < α ∧ ∀ n : ℕ, ∀ y : Fin (n+1) → ℝ,
      α*(y ⬝ᵥ y) ≤ sourceMomentQuadratic h s (n+1) y := by
  rintro ⟨α,hα,hc⟩
  have ht : Filter.Tendsto (fun n : ℕ => (22/175:ℝ)^(n+1)) Filter.atTop (𝓝 0) := by
    simpa only [zero_mul,pow_succ] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0:ℝ) ≤ 22/175) (by norm_num : (22/175:ℝ) < 1)).mul_const (22/175:ℝ)
  have he := (tendsto_order.mp ht).2 α hα
  obtain ⟨n,hn⟩ := he.exists
  exact (not_lt_of_ge (native_coercivity_upper_bound s n α (hc n))) hn

/-- A finite proxy counterexample, NOT a modification of the native source. -/
def proxyMoments (k : ℕ) : ℝ := (1/2:ℝ)^k*(if k=2 then 1/2 else 1)

theorem proxyMoments_positive (k : ℕ) : 0 < proxyMoments k := by
  unfold proxyMoments
  split_ifs <;> positivity

theorem proxyMoments_geometric_bound (k : ℕ) : proxyMoments k ≤ (1/2:ℝ)^k := by
  unfold proxyMoments
  split_ifs <;> nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) k]

theorem schur_one_formula (m : ℕ → ℝ) (s : ℕ) :
    sourceMomentSchur m s 1 = m (2+s)-m (1+s)^2/m s := by
  simp [sourceMomentSchur,sourceMomentCoupling,sourceMomentMatrix,Matrix.inv_subsingleton,
    Matrix.mulVec,dotProduct,pow_two]
  ring

/-- Positive entries and geometric decay do not imply the next Schur sign. -/
theorem proxy_schur_negative : sourceMomentSchur proxyMoments 0 1 = -1/8 := by
  rw [schur_one_formula]
  norm_num [proxyMoments]

/-- A positive trial energy alone is an UPPER bound on sigma, and can be
positive while sigma is negative. It is not a residual-error certificate. -/
theorem positive_trial_energy_negative_schur :
    sourceTrialEnergy proxyMoments 0 1 0 = 1/8 ∧
      sourceMomentSchur proxyMoments 0 1 < 0 := by
  constructor
  · rw [sourceTrialEnergy_expansion]
    norm_num [proxyMoments,sourceMomentQuadratic]
  · rw [proxy_schur_negative]
    norm_num

end
end CarryResidualObstructions
