import CriticalGridPolynomial

namespace CarryCriticalGrid
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryCommutatorControl CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryMixedParity CarryCrossRadial CarryGreenLeading CarryGreenCubic CarryOddGreen CarryCubicOdd CarryCurvatureGreen CarryOddCauchy NativeLaguerre NativeCauchyPorts
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4800000

/-- Fixed algebraic coordinate scale: squared inverse ORIGINAL radial kappa. -/
abbrev squaredScale (k : ℕ) : ℂ := ((k:ℂ)+1)⁻¹^2

/-- Reversible READOUT coordinates, not a normalization of physical states. -/
def normalizedFourSamples (k : ℕ) (w : ℕ → ℂ) (j : Fin 4) : ℂ :=
  ((k:ℂ)+1)*w j/((j:ℂ)+1)

abbrev nativeFourSamples (k : ℕ) : Fin 4 → ℂ :=
  normalizedFourSamples k (responseSamples (radialStep k))

theorem squared_scale_nonzero (k : ℕ) : squaredScale k≠0 := by
  have hk : (k:ℂ)+1≠0 := by exact_mod_cast (by omega : k+1≠0)
  exact pow_ne_zero 2 (inv_ne_zero hk)

theorem squared_scale_real_positive (k : ℕ) :
    (squaredScale k).im=0 ∧ 0<(squaredScale k).re := by
  have he : squaredScale k=((((k:ℝ)+1)⁻¹)^2:ℝ) := by
    simp [squaredScale]
  rw [he]
  refine ⟨rfl,?_⟩
  change 0<(((k:ℝ)+1)⁻¹)^2
  positivity

/-- Reality is a property of this readout, not a collapse of physical channels. -/
theorem native_four_samples_real (k : ℕ) (j : Fin 4) :
    conj (nativeFourSamples k j)=nativeFourSamples k j := by
  unfold nativeFourSamples normalizedFourSamples
  simp only [map_div₀,map_mul,map_add,map_natCast,map_one,
    response_samples_real (radialStep k)]

/-- Every normalized coordinate recovers the SAME original response sample. -/
theorem normalized_four_samples_recover (k : ℕ) (w : ℕ → ℂ) (j : Fin 4) :
    (((j:ℂ)+1)/((k:ℂ)+1))*normalizedFourSamples k w j=w j := by
  have hk : (k:ℂ)+1≠0 := by exact_mod_cast (by omega : k+1≠0)
  have hj : (j:ℂ)+1≠0 := by exact_mod_cast (by omega : (j:ℕ)+1≠0)
  unfold normalizedFourSamples
  field_simp

/-- EXACT polarized change of readout coordinates. All 16 Cauchy crosses and
both ordered kernels are retained; no analytic assumption or moment enters. -/
theorem critical_readout_squared_grid (a b : ℝ) (k : ℕ) (w : ℕ → ℂ) :
    ((k:ℂ)+1)*(criticalSampleReadout a b k w+criticalSampleReadout b a k w)=
      gridBalance (squaredScale k) (a:ℂ) (b:ℂ) (normalizedFourSamples k w) := by
  have hk : (k:ℂ)+1≠0 := by exact_mod_cast (by omega : k+1≠0)
  unfold criticalSampleReadout gridBalance criticalGridPolynomial gridThird gridSecondRight gridSecond
  norm_num [criticalBeta,Fin.sum_univ_succ,squaredNode,normalizedFourSamples,squaredScale]
  field_simp
  ring

/-- Original TWO-leg, nine-cross Green balance, before its canonical limit. -/
theorem native_critical_grid_exact (a b : ℝ) (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    ∀ᶠ k : ℕ in atTop,
      crossGreenPair eta h0 h1 k k (criticalOddSource a k) (criticalOddSource b k)=
        gridBalance (squaredScale k) (a:ℂ) (b:ℂ) (nativeFourSamples k) := by
  filter_upwards [critical_green_readout_exact a b eta h0 h1] with k hk
  exact hk.trans (critical_readout_squared_grid a b k (responseSamples (radialStep k)))

/-- Exact extraction of the first, second and third native grid curvatures. -/
theorem native_critical_curvatures_exact (a b : ℝ) (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    ∀ᶠ k : ℕ in atTop,
      crossGreenPair eta h0 h1 k k (criticalOddSource a k) (criticalOddSource b k)=
        -gridThird (squaredScale k) (nativeFourSamples k)-
        ((a:ℂ)+(b:ℂ))*(gridSecond (squaredScale k) (nativeFourSamples k)+
          28*squaredScale k*gridThird (squaredScale k) (nativeFourSamples k))-
        (a:ℂ)*(b:ℂ)*gridFirst (squaredScale k) (nativeFourSamples k) := by
  filter_upwards [native_critical_grid_exact a b eta h0 h1] with k hk
  rw [hk,critical_grid_curvatures _ (squared_scale_nonzero k)]

/-- Finite-grid product and its signed defect in the SAME original response. -/
theorem native_critical_product_defect_exact (a b : ℝ) (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    ∀ᶠ k : ℕ in atTop,
      crossGreenPair eta h0 h1 k k (criticalOddSource a k) (criticalOddSource b k)=
        -gridThird (squaredScale k) (fun j =>
          (1+(a:ℂ)*(squaredNode (squaredScale k) j+12*squaredScale k))*
          (1+(b:ℂ)*(squaredNode (squaredScale k) j+12*squaredScale k))*nativeFourSamples k j)+
        49*(a:ℂ)*(b:ℂ)*squaredScale k*
          gridThird (squaredScale k) (fun j => squaredNode (squaredScale k) j*nativeFourSamples k j) := by
  filter_upwards [native_critical_grid_exact a b eta h0 h1] with k hk
  rw [hk,critical_grid_product_defect]

/-- Compatibility with the original canonical moments AFTER full synthesis.
This reuses their existing provenance, without any sign assumption. -/
theorem native_critical_grid_tendsto (a b : ℝ) :
    Tendsto (fun k : ℕ => gridBalance (squaredScale k) (a:ℂ) (b:ℂ) (nativeFourSamples k)) atTop
      (nhds ((h 3-(a+b)*h 2+a*b*h 1:ℝ):ℂ)) := by
  apply (critical_signed_tendsto a b).congr'
  filter_upwards [critical_signed_readout_exact a b] with k hk
  exact hk.trans (critical_readout_squared_grid a b k (responseSamples (radialStep k)))

/-- The true odd Schur specialization, not an assumed norm square. -/
theorem native_critical_grid_schur_tendsto (hh : h 1≠0) :
    Tendsto (fun k : ℕ => gridBalance (squaredScale k) ((h 2/h 1:ℝ):ℂ) ((h 2/h 1:ℝ):ℂ) (nativeFourSamples k)) atTop
      (nhds ((h 3-h 2^2/h 1:ℝ):ℂ)) := by
  have he := native_critical_grid_tendsto (h 2/h 1) (h 2/h 1)
  convert he using 1
  congr 2
  field_simp
  ring


/-- The grid really coalesces at the ORIGINAL radial rate. -/
theorem squared_scale_tendsto_zero : Tendsto squaredScale atTop (nhds 0) := by
  change Tendsto (fun k : ℕ => (((k:ℂ)+1)⁻¹)^2) atTop (nhds 0)
  have ht : Tendsto (fun k : ℕ => (radialStep k:ℂ)) atTop (nhds 0) := by
    simpa only [Function.comp_def,Complex.ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp radial_step_tendsto
  simpa [squaredScale,radialStep] using ht.pow 2

/-- Native third curvature: its sign is not assumed. -/
theorem native_grid_third_tendsto :
    Tendsto (fun k : ℕ => gridThird (squaredScale k) (nativeFourSamples k)) atTop (nhds (-(h 3:ℂ))) := by
  simpa [gridBalance,criticalGridPolynomial] using (native_critical_grid_tendsto 0 0).neg

/-- The mixed entry is recovered by POLARIZATION, not just diagonal norms. -/
theorem native_grid_mixed_tendsto :
    Tendsto (fun k : ℕ => gridSecond (squaredScale k) (nativeFourSamples k)+
      28*squaredScale k*gridThird (squaredScale k) (nativeFourSamples k)) atTop (nhds (h 2:ℂ)) := by
  have he := (native_critical_grid_tendsto 0 0).sub (native_critical_grid_tendsto 1 0)
  convert he using 1
  · funext k
    simpa only [Complex.ofReal_zero,Complex.ofReal_one] using
      grid_mixed_from_pairs (squaredScale k) (squared_scale_nonzero k) (nativeFourSamples k)
  · push_cast
    ring

theorem native_grid_first_tendsto :
    Tendsto (fun k : ℕ => gridFirst (squaredScale k) (nativeFourSamples k)) atTop (nhds (-(h 1:ℂ))) := by
  have he := (((native_critical_grid_tendsto 1 1).neg.add
    (native_critical_grid_tendsto 1 0)).add (native_critical_grid_tendsto 0 1)).sub
      (native_critical_grid_tendsto 0 0)
  convert he using 1
  · funext k
    simpa only [Complex.ofReal_zero,Complex.ofReal_one] using
      grid_first_from_pairs (squaredScale k) (squared_scale_nonzero k) (nativeFourSamples k)
  · push_cast
    ring

theorem native_grid_second_tendsto :
    Tendsto (fun k : ℕ => gridSecond (squaredScale k) (nativeFourSamples k)) atTop (nhds (h 2:ℂ)) := by
  have hz := (tendsto_const_nhds (x:=(28:ℂ))).mul (squared_scale_tendsto_zero.mul native_grid_third_tendsto)
  have he := native_grid_mixed_tendsto.sub hz
  simp only [zero_mul,mul_zero,sub_zero] at he
  apply he.congr'
  filter_upwards [] with k
  ring

/-- Retains the coordinate multiplier INSIDE the same third divided difference. -/
theorem native_grid_node_third_tendsto :
    Tendsto (fun k : ℕ => gridThird (squaredScale k)
      (fun j => squaredNode (squaredScale k) j*nativeFourSamples k j)) atTop (nhds (h 2:ℂ)) := by
  have hz := (tendsto_const_nhds (x:=(16:ℂ))).mul (squared_scale_tendsto_zero.mul native_grid_third_tendsto)
  have he := native_grid_second_tendsto.add hz
  simp only [zero_mul,mul_zero,add_zero] at he
  apply he.congr'
  filter_upwards [] with k
  symm
  rw [grid_third_mul_node _ (squared_scale_nonzero k)]
  ring

/-- The correction from the EXACT original product-defect identity. -/
abbrev nativeGridDefect (a b : ℝ) (k : ℕ) : ℂ :=
  49*(a:ℂ)*(b:ℂ)*squaredScale k*
    gridThird (squaredScale k) (fun j => squaredNode (squaredScale k) j*nativeFourSamples k j)

/-- A rate law: the defect divided by epsilon tends to 49 a b h2.
No sign of h2, or of the Schur pivot, enters. -/
theorem native_grid_defect_scaled_tendsto (a b : ℝ) :
    Tendsto (fun k : ℕ => nativeGridDefect a b k/squaredScale k) atTop
      (nhds (49*(a:ℂ)*(b:ℂ)*(h 2:ℂ))) := by
  have he := (tendsto_const_nhds (x:=(49*(a:ℂ)*(b:ℂ)))).mul native_grid_node_third_tendsto
  apply he.congr'
  filter_upwards [] with k
  unfold nativeGridDefect
  field_simp [squared_scale_nonzero k]

theorem native_grid_defect_tendsto_zero (a b : ℝ) :
    Tendsto (nativeGridDefect a b) atTop (nhds 0) := by
  have he := squared_scale_tendsto_zero.mul (native_grid_defect_scaled_tendsto a b)
  simp only [zero_mul] at he
  apply he.congr'
  filter_upwards [] with k
  field_simp [squared_scale_nonzero k]



/-- The FOUR readouts coalesce to h0, although their scaled curvatures do not.
This is about samples of the same response, not convergence of physical states. -/
theorem native_four_sample_tendsto (j : Fin 4) :
    Tendsto (fun k : ℕ => nativeFourSamples k j) atTop (nhds (h 0:ℂ)) := by
  let t (k : ℕ) : ℂ := ((j:ℂ)+1)*((k:ℂ)+1)⁻¹
  have hd : Tendsto (fun k : ℕ => ((k:ℂ)+1)⁻¹) atTop (nhds 0) := by
    simpa [radialStep,Function.comp_def] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp radial_step_tendsto
  have ht : Tendsto t atTop (nhds 0) := by
    simpa [t] using (tendsto_const_nhds (x:=((j:ℂ)+1))).mul hd
  have hj : (j:ℂ)+1≠0 := by exact_mod_cast (by omega : (j:ℕ)+1≠0)
  have hn (k : ℕ) : t k≠0 := by
    have hk : (k:ℂ)+1≠0 := by exact_mod_cast (by omega : k+1≠0)
    exact mul_ne_zero hj (inv_ne_zero hk)
  have heq (k : ℕ) : nativeFourSamples k j=responseReadout (t k)/t k := by
    have hk : (k:ℂ)+1≠0 := by exact_mod_cast (by omega : k+1≠0)
    unfold nativeFourSamples normalizedFourSamples responseSamples t radialStep
    push_cast
    field_simp
  have hR := (native_remainder_analytic 1).continuousAt.tendsto.comp ht
  have hl := (tendsto_const_nhds (x:=(h 0:ℂ))).add ((ht.pow 2).mul hR)
  simp only [zero_pow (by decide : 2≠0),zero_mul,add_zero] at hl
  apply hl.congr'
  filter_upwards [ht.eventually (native_response_expansion 1)] with k hk
  rw [heq k,hk]
  norm_num [oddTaylor]
  field_simp [hn k]

/-- Full Newton data retain the four original canonical coefficients in order. -/
theorem native_newton_data_tendsto :
    Tendsto (fun k : ℕ => (nativeFourSamples k 0,
      gridFirst (squaredScale k) (nativeFourSamples k),
      gridSecond (squaredScale k) (nativeFourSamples k),
      gridThird (squaredScale k) (nativeFourSamples k))) atTop
      (nhds ((h 0:ℂ),-(h 1:ℂ),(h 2:ℂ),-(h 3:ℂ))) := by
  exact (native_four_sample_tendsto 0).prodMk_nhds
    (native_grid_first_tendsto.prodMk_nhds
      (native_grid_second_tendsto.prodMk_nhds native_grid_third_tendsto))


end
end CarryCriticalGrid
