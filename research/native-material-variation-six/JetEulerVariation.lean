import PhysicalMaterialVariation

namespace CarryMaterialVariation
open CarrySelfAdjointOperator CarryMovingRadial CarryStencilBoundary NativeLaguerre
open CarrySelfAdjointOperator.PhysicalSewing Filter Topology
open scoped BigOperators ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- Literal existing factorial-normalized stencil, restricted to a finite
prefix. Jet order m is not the material clock or vertical Carry depth. -/
def radialJetVector (N m : ℕ) (t : ℝ) : Fin N → ℂ := fun i =>
  ((m.factorial:ℂ)*(Complex.I*(t:ℂ))^m)⁻¹*completedGreenForwardWeight m i

theorem radial_jet_vector_at_grid (N m k : ℕ) (i : Fin N) :
    radialJetVector N m (radialFourSourceStep k) i=radialJetCoefficients k m i := by
  simp only [radialJetVector,radialJetCoefficients,Finsupp.smul_apply,smul_eq_mul,
    raw_stencil_apply,canonicalCompletedC3RadialSecondStep,
    canonicalGreenJetStep_eq_radialFourSourceStep]


theorem radial_jet_prefix_support (N m k : ℕ) (hm : m<N) :
    (radialJetCoefficients k m).support⊆Finset.range N := by
  intro j hj
  by_contra hn
  have hN : N≤j := Nat.le_of_not_lt (fun h => hn (Finset.mem_range.mpr h))
  have hmj : m<j := lt_of_lt_of_le hm hN
  have hz : radialJetCoefficients k m j=0 := by
    simp [radialJetCoefficients,raw_stencil_apply,smul_eq_mul,
      completedGreenForwardWeight,Nat.choose_eq_zero_of_lt hmj]
  exact (Finsupp.mem_support_iff.mp hj) hz

theorem radial_jet_curve_original (N m k : ℕ) (hm : m<N) :
    curveState N (radialFourSourceStep k) (radialJetVector N m (radialFourSourceStep k))=
      physicalCompletedFiniteSource k (radialJetCoefficients k m) := by
  rw [curve_eq_original]
  have he : radialJetVector N m (radialFourSourceStep k)=
      fun i : Fin N => radialJetCoefficients k m i := by
    funext i; exact radial_jet_vector_at_grid N m k i
  rw [he,finite_coefficients_restrict N _ (radial_jet_prefix_support N m k hm)]

theorem radial_jet_curve_complete_jet (N m k : ℕ) (hm : m<N) :
    curveState N (radialFourSourceStep k) (radialJetVector N m (radialFourSourceStep k))=
      projectiveChiralDifferenceJet k m := by
  rw [radial_jet_curve_original N m k hm,radial_jet_original_source]

/-- All jet orders: the actual raw coefficient carries degree -m in h. -/
theorem radial_jet_hasDerivAt (N m : ℕ) (t : ℝ) (ht : t≠0) (i : Fin N) :
    HasDerivAt (fun h : ℝ => radialJetVector N m h i)
      (-(m:ℂ)/(t:ℂ)*radialJetVector N m t i) t := by
  cases m with
  | zero => simpa [radialJetVector] using hasDerivAt_const t (completedGreenForwardWeight 0 i)
  | succ m =>
    have hn : (t:ℂ)≠0 := by exact_mod_cast ht
    have hf : ((m+1).factorial:ℂ)≠0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hi : HasDerivAt (fun z : ℂ => Complex.I*z) Complex.I (t:ℂ) := by
      simpa using (hasDerivAt_id (t:ℂ)).const_mul Complex.I
    have hd : ((m+1).factorial:ℂ)*(Complex.I*(t:ℂ))^(m+1)≠0 :=
      mul_ne_zero hf (pow_ne_zero _ (mul_ne_zero Complex.I_ne_zero hn))
    have hh := ((((hasDerivAt_const (t:ℂ) ((m+1).factorial:ℂ)).mul
      (hi.pow (m+1))).inv hd).mul_const (completedGreenForwardWeight (m+1) i))
    have he : HasDerivAt (fun z : ℂ =>
        (((m+1).factorial:ℂ)*(Complex.I*z)^(m+1))⁻¹*completedGreenForwardWeight (m+1) i)
        (-((m+1:ℕ):ℂ)/(t:ℂ)*radialJetVector N (m+1) t i) (t:ℂ) := by
      convert hh using 1
      all_goals try rfl
      unfold radialJetVector
      simp only [Pi.mul_apply,Pi.pow_apply,Nat.add_sub_cancel]
      field_simp [hf,hn,Complex.I_ne_zero]
      simp only [pow_succ,mul_pow]
      ring
    exact he.comp_ofReal

theorem materialPair_scale_inputs (N : ℕ) (r x y : Fin N → ℂ) (a b : ℂ) :
    materialPair N r (fun i => a*x i) (fun i => b*y i)=
      conj a*b*materialPair N r x y := by
  unfold materialPair
  simp only [map_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem materialPair_linear_readout (N : ℕ) (r s x y : Fin N → ℂ) (a b : ℂ) :
    materialPair N (fun i => a*r i+b*s i) x y=
      a*materialPair N r x y+b*materialPair N s x y := by
  unfold materialPair
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Exact all-order jet transport: the completed variation uses
h*rho'-(m+n+1)*rho, with both inputs and all crosses retained. -/
theorem jet_material_variation (N m n : ℕ) (t : ℝ) (ht : t≠0)
    (r dr x y : Fin N → ℂ) :
    materialVariation N t r dr x (fun i => -(m:ℂ)/(t:ℂ)*x i)
      y (fun i => -(n:ℂ)/(t:ℂ)*y i)=
        (2/(t:ℂ)^2)*materialPair N
          (fun i => (t:ℂ)*dr i-((m+n+1:ℕ):ℂ)*r i) x y := by
  have hleft : materialPair N r (fun i => -(m:ℂ)/(t:ℂ)*x i) y=
      (-(m:ℂ)/(t:ℂ))*materialPair N r x y := by
    simpa only [one_mul,mul_one,map_div₀,map_neg,map_natCast,Complex.conj_ofReal] using
      materialPair_scale_inputs N r x y (-(m:ℂ)/(t:ℂ)) 1
  have hright : materialPair N r x (fun i => -(n:ℂ)/(t:ℂ)*y i)=
      (-(n:ℂ)/(t:ℂ))*materialPair N r x y := by
    simpa only [one_mul,mul_one,map_one] using materialPair_scale_inputs N r x y 1 (-(n:ℂ)/(t:ℂ))
  unfold materialVariation
  rw [hleft,hright,materialPair_affine]
  have hr := materialPair_linear_readout N dr r x y (t:ℂ) (-((m+n+1:ℕ):ℂ))
  simp only [sub_eq_add_neg,neg_mul] at hr ⊢
  rw [hr]
  have hn : (t:ℂ)≠0 := by exact_mod_cast ht
  push_cast
  field_simp [hn]
  ring


/-- Action on a Taylor layer: the canonical degree m+n+1 has coefficient
zero under the completed Euler variation. This is a layer identity, not a
substitution of the original source by a monomial. -/
theorem jet_kernel_monomial (m n k : ℕ) (z a : ℂ) :
    z*((k+1:ℕ):ℂ)*z^k*a-((m+n+1:ℕ):ℂ)*(z^(k+1)*a)=
      (((k+1:ℕ):ℂ)-((m+n+1:ℕ):ℂ))*z^(k+1)*a := by
  rw [pow_succ]
  ring

theorem canonical_layer_annihilated (m n : ℕ) (z a : ℂ) :
    z*((m+n+1:ℕ):ℂ)*z^(m+n)*a-
      ((m+n+1:ℕ):ℂ)*(z^(m+n+1)*a)=0 := by
  simpa only [sub_self,zero_mul] using jet_kernel_monomial m n (m+n) z a

theorem physical_jet_material_derivative (N m n : ℕ) (t : ℝ) (ht : 0<t)
    (hD : ∀ i : Fin N, point t i∈completedNativeHeightDomain)
    (hF : ∀ i : Fin N, completedNativeOperatorCharacteristic (point t i)≠0)
    (hP : ∀ i : Fin N, completedNativePositiveHermiteBiehlerCoordinate (point t i)≠0) :
    deriv (fun h => 2*canonicalCompletedNativeProjectiveChiralForm
      (curveState N h (radialJetVector N m h)) (curveState N h (radialJetVector N n h))) t=
      (2/(t:ℂ)^2)*materialPair N
        (fun i => (t:ℂ)*rhoVelocity N t i-((m+n+1:ℕ):ℂ)*CarryMovingRadial.rho t i)
        (radialJetVector N m t) (radialJetVector N n t) := by
  rw [physical_material_derivative N _ _ t ht
    (fun i => (radial_jet_hasDerivAt N m t ht.ne' i).differentiableAt)
    (fun i => (radial_jet_hasDerivAt N n t ht.ne' i).differentiableAt) hD hF hP]
  have hm : rawVelocity N (radialJetVector N m) t=
      fun i => -(m:ℂ)/(t:ℂ)*radialJetVector N m t i := by
    funext i; exact (radial_jet_hasDerivAt N m t ht.ne' i).deriv
  have hn : rawVelocity N (radialJetVector N n) t=
      fun i => -(n:ℂ)/(t:ℂ)*radialJetVector N n t i := by
    funext i; exact (radial_jet_hasDerivAt N n t ht.ne' i).deriv
  rw [hm,hn]
  exact jet_material_variation N m n t ht.ne' _ _ _ _

end
end CarryMaterialVariation
