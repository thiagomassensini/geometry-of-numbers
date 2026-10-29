import ColumnAsymptotics

namespace CarryPhysicalTrace
open CarrySelfAdjointOperator CarrySelfAdjointOperator.NativeLaguerre
open CPFormal.Analytic.Cp Filter Topology
noncomputable section
set_option autoImplicit false

/-- The imaginary part is arbitrary: the original material phase is retained. -/
theorem critical_column_readout_norm_sq (s : ℂ) (hs : s.re = 1/2) (j : ℕ) :
    ‖(Real.sqrt ((j+j+2 : ℕ) : ℝ) : ℂ) * positiveDirichletValue s j‖^2 = 2 := by
  have hp : 0 < ((j+1 : ℕ) : ℝ) := by positivity
  have hr : (((j+1 : ℕ) : ℝ)^(-(1/2 : ℝ)))^2 = (((j+1 : ℕ) : ℝ))⁻¹ := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hp.le]
    norm_num [Real.rpow_neg_one]
  rw [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,
    Real.sq_sqrt (by positivity),norm_positiveDirichletValue,hs,hr]
  have hd : ((j+j+2 : ℕ) : ℝ) = 2*((j+1 : ℕ) : ℝ) := by push_cast; ring
  rw [hd,mul_assoc,mul_inv_cancel₀ hp.ne',mul_one]

/-- NO-GO for a bounded readout on this SAME L2 closure, not for the native
Dirichlet synthesis on its appropriate domain and not for every Gram candidate. -/
theorem no_bounded_critical_dirichlet_columns (s : ℂ) (hs : s.re = 1/2) :
    ¬∃ L : PhysicalCauchySpace →L[ℂ] ℂ,
      ∀ j, L (physicalCauchyFeature j) = positiveDirichletValue s j := by
  rintro ⟨L,hL⟩
  have hc := bounded_readout_unit_tendsto_zero L
  have he (j : ℕ) : ‖L (unitColumn j)‖^2 = 2 := by
    rw [unitColumn,map_smul,smul_eq_mul,hL]
    exact critical_column_readout_norm_sq s hs j
  have hz := (tendsto_zero_iff_norm_tendsto_zero.mp hc).pow 2
  simp only [zero_pow (by norm_num : 2 ≠ 0),he] at hz
  have hh : (2 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hz
  norm_num at hh

theorem no_bounded_critical_dirichlet_extension (s : ℂ) (hs : s.re = 1/2) :
    ¬∃ L : PhysicalCauchySpace →L[ℂ] ℂ,
      ∀ f : EndpointDomain, L (f : PhysicalCauchySpace) = dirichletTrace s f := by
  rintro ⟨L,hL⟩
  apply no_bounded_critical_dirichlet_columns s hs
  refine ⟨L,fun j => ?_⟩
  simpa only [domain_column_coe,dirichlet_trace_column] using hL (domainColumn j)

end
end CarryPhysicalTrace
