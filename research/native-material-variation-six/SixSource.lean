import PhysicalMaterialVariation

namespace CarryMaterialVariation
open CarrySelfAdjointOperator CarryMovingRadial CarryStencilBoundary NativeLaguerre
open CarrySelfAdjointOperator.PhysicalSewing Filter Topology
open scoped BigOperators ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- Free trial family in the ORIGINAL jets 1,3,5, before moments are read. -/
def sixInput (u v : ℝ) (k : ℕ) : ℕ →₀ ℂ :=
  radialJetCoefficients k 5+(u:ℂ) • radialJetCoefficients k 3+
    (v:ℂ) • radialJetCoefficients k 1

def sixWeight (u v : ℝ) (z : ℂ) : Fin 6 → ℂ :=
  ![-1+20*(u:ℂ)*z^2-120*(v:ℂ)*z^4,
    5-60*(u:ℂ)*z^2+120*(v:ℂ)*z^4,
    -10+60*(u:ℂ)*z^2,10-20*(u:ℂ)*z^2,-5,1]

def sixRaw (u v : ℝ) (z : ℂ) : Fin 6 → ℂ :=
  fun i => -Complex.I/(120*z^5)*sixWeight u v z i

theorem six_input_outside (u v : ℝ) (k j : ℕ) (hj : 6≤j) : sixInput u v k j=0 := by
  have h5 : 5<j := by omega
  have h3 : 3<j := by omega
  have h1 : 1<j := by omega
  simp [sixInput,radialJetCoefficients,smul_eq_mul,
    raw_stencil_apply,completedGreenForwardWeight,Nat.choose_eq_zero_of_lt h5,
    Nat.choose_eq_zero_of_lt h3,Nat.choose_eq_zero_of_lt h1]

theorem six_input_support (u v : ℝ) (k : ℕ) : (sixInput u v k).support⊆Finset.range 6 := by
  intro j hj
  by_contra hn
  have hs : 6≤j := Nat.le_of_not_lt (fun h => hn (Finset.mem_range.mpr h))
  exact (Finsupp.mem_support_iff.mp hj) (six_input_outside u v k j hs)

/-- Exact coefficients, phases and factorials of the original source. -/
theorem six_raw_at_grid (u v : ℝ) (k : ℕ) (i : Fin 6) :
    sixRaw u v (canonicalGreenJetStep k) i=sixInput u v k i := by
  have hk : (k:ℂ)+1≠0 := by exact_mod_cast (by positivity : (k:ℝ)+1≠0)
  fin_cases i <;> norm_num [sixRaw,sixWeight,sixInput,radialJetCoefficients,
    Finsupp.smul_apply,smul_eq_mul,raw_stencil_apply,completedGreenForwardWeight,
    canonicalCompletedC3RadialSecondStep,canonicalGreenJetStep,
    Complex.I_pow_eq_pow_mod,Complex.I_sq] <;> field_simp [hk] <;> ring_nf <;>
    norm_num [Complex.I_pow_eq_pow_mod,Complex.I_sq,Nat.choose] <;>
    ring_nf <;> norm_num [Complex.I_sq] <;> ring

theorem six_curve_eq_original (u v : ℝ) (k : ℕ) :
    curveState 6 (radialFourSourceStep k) (sixRaw u v (canonicalGreenJetStep k))=
      physicalCompletedFiniteSource k (sixInput u v k) := by
  rw [curve_eq_original]
  have he : sixRaw u v (canonicalGreenJetStep k)=fun i : Fin 6 => sixInput u v k i := by
    funext i; exact six_raw_at_grid u v k i
  rw [he,finite_coefficients_restrict 6 _ (six_input_support u v k)]

theorem six_raw_differentiable (u v t : ℝ) (ht : 0<t) (i : Fin 6) :
    DifferentiableAt ℝ (fun h : ℝ => sixRaw u v (h:ℂ) i) t := by
  have hn : (t:ℂ)≠0 := by exact_mod_cast ht.ne'
  have hd : (120:ℂ)*(t:ℂ)^5≠0 := mul_ne_zero (by norm_num) (pow_ne_zero _ hn)
  have ha : AnalyticAt ℂ (fun z => sixRaw u v z i) (t:ℂ) := by
    fin_cases i <;> dsimp [sixRaw,sixWeight] <;> fun_prop (disch := assumption)
  exact ha.differentiableAt.hasDerivAt.comp_ofReal.differentiableAt

/-- Closed material variation applies to the SAME six-address source;
regularity and input differentiability are discharged from the source. -/
theorem six_closed_material_derivative (u v : ℝ) :
    ∀ᶠ t : ℝ in nhds 0, 0<t →
      deriv (fun h => 2*canonicalCompletedNativeProjectiveChiralForm
        (curveState 6 h (sixRaw u v (h:ℂ))) (curveState 6 h (sixRaw u v (h:ℂ)))) t=
        materialVariation 6 t (fun i => CarryMovingRadial.rho t i) (rhoVelocity 6 t)
          (sixRaw u v (t:ℂ)) (rawVelocity 6 (fun h => sixRaw u v (h:ℂ)) t)
          (sixRaw u v (t:ℂ)) (rawVelocity 6 (fun h => sixRaw u v (h:ℂ)) t) := by
  filter_upwards [curve_regular_eventually 6] with t ht hp
  exact physical_material_derivative 6 _ _ t hp
    (six_raw_differentiable u v t hp) (six_raw_differentiable u v t hp)
    (fun i => (ht i).1) (fun i => (ht i).2.1) (fun i => (ht i).2.2)

end
end CarryMaterialVariation
