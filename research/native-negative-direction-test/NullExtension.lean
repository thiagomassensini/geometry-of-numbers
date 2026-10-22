import SourceChart

namespace CarryNegativeDirection
open CarrySelfAdjointOperator ChiralReturn CarryCriticalSource
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem source_quadratic_smul (m : ℕ → ℝ) (s n : ℕ) (a : ℝ) (z : Fin n → ℝ) :
    sourceMomentQuadratic m s n (a • z)=a^2*sourceMomentQuadratic m s n z := by
  simp only [sourceMomentQuadratic,star_trivial,Matrix.mulVec_smul,smul_dotProduct,
    dotProduct_smul,smul_eq_mul]
  ring

/-- Explicit witness of a new negative direction after a null prefix direction
with a nonzero new crossing. No inverse or positivity hypothesis is required. -/
def nullCouplingWitness (m : ℕ → ℝ) (s n : ℕ) (z : Fin n → ℝ) : Fin (n+1) → ℝ :=
  Fin.snoc ((-((m (2*n+s)^2+1)/(2*(sourceMomentCoupling m s n ⬝ᵥ z)))) • z) 1

theorem null_coupling_witness_energy (m : ℕ → ℝ) (s n : ℕ) (z : Fin n → ℝ)
    (hz : sourceMomentQuadratic m s n z=0)
    (hb : sourceMomentCoupling m s n ⬝ᵥ z≠0) :
    sourceMomentQuadratic m s (n+1) (nullCouplingWitness m s n z)=
      m (2*n+s)-m (2*n+s)^2-1 := by
  rw [nullCouplingWitness,sourceMomentQuadratic_snoc,source_quadratic_smul,hz]
  simp only [mul_zero,zero_add,dotProduct_smul,smul_eq_mul,one_pow,mul_one]
  field_simp
  ring

theorem null_coupling_witness_negative (m : ℕ → ℝ) (s n : ℕ) (z : Fin n → ℝ)
    (hz : sourceMomentQuadratic m s n z=0)
    (hb : sourceMomentCoupling m s n ⬝ᵥ z≠0) :
    sourceMomentQuadratic m s (n+1) (nullCouplingWitness m s n z)<0 := by
  rw [null_coupling_witness_energy m s n z hz hb]
  nlinarith [sq_nonneg (m (2*n+s)-(1:ℝ)/2)]

/-- A necessary range-compatibility condition for PSD extension, even when the old prefix is singular. -/
theorem psd_extension_annihilates_old_null_crossings (m : ℕ → ℝ) (s n : ℕ)
    (hp : (sourceMomentMatrix m s (n+1)).PosSemidef)
    (z : Fin n → ℝ) (hz : sourceMomentQuadratic m s n z=0) :
    sourceMomentCoupling m s n ⬝ᵥ z=0 := by
  by_contra hb
  have hn := null_coupling_witness_negative m s n z hz hb
  exact (not_lt_of_ge (hp.dotProduct_mulVec_nonneg (nullCouplingWitness m s n z))) hn

end
end CarryNegativeDirection
