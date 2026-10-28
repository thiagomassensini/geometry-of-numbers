import MaterialVariation
import RadialRegularity

namespace CarryAllOrderTail
open CarrySelfAdjointOperator CarryMaterialVariation Filter Topology
open scoped BigOperators ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

/-- Pairwise bound for arbitrary independent complex inputs. The denominator
and both addresses are exactly those of the original Cauchy pairing. -/
theorem cross_error_bound (i j : ℕ) (x y a b : ℂ) (ε : ℝ)
    (hε : 0≤ε) (ha : ‖a‖≤ε) (hb : ‖b‖≤ε) :
    ‖conj x*y*(a+b)/((i:ℂ)+(j:ℂ)+2)‖ ≤ ‖x‖*‖y‖*ε := by
  have hd : (2:ℝ)≤(i:ℝ)+(j:ℝ)+2 := by
    have hi : (0:ℝ) ≤ i := Nat.cast_nonneg i
    have hj : (0:ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  have hnorm : ‖(i:ℂ)+(j:ℂ)+2‖=(i:ℝ)+(j:ℝ)+2 := by
    have hc := Complex.norm_real ((i:ℝ)+(j:ℝ)+2)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hc
    push_cast at hc
    exact hc
  rw [norm_div,norm_mul,norm_mul,Complex.norm_conj,hnorm]
  apply (div_le_iff₀ (by linarith : 0<(i:ℝ)+(j:ℝ)+2)).mpr
  have hs : ‖a+b‖≤2*ε := (norm_add_le a b).trans (by linarith)
  have hm := mul_le_mul_of_nonneg_left hs (mul_nonneg (norm_nonneg x) (norm_nonneg y))
  have hx := mul_nonneg (mul_nonneg (norm_nonneg x) (norm_nonneg y)) hε
  nlinarith

/-- Arbitrary finite dimension, no positivity: all ordered crosses survive
before taking norms and the factor is determined by the Cauchy kernel. -/
theorem material_pair_uniform_error (N : ℕ) (r s x y : Fin N → ℂ) (ε : ℝ)
    (hε : 0≤ε) (hr : ∀ i, ‖r i-s i‖≤ε) :
    ‖materialPair N r x y-materialPair N s x y‖ ≤
      ε*(∑ i : Fin N, ‖x i‖)*(∑ j : Fin N, ‖y j‖) := by
  unfold materialPair
  simp_rw [← Finset.sum_sub_distrib]
  have he (i j : Fin N) :
      conj (x i)*y j*(r i+r j)/((i:ℂ)+(j:ℂ)+2)-
        conj (x i)*y j*(s i+s j)/((i:ℂ)+(j:ℂ)+2)=
      conj (x i)*y j*((r i-s i)+(r j-s j))/((i:ℂ)+(j:ℂ)+2) := by ring
  simp_rw [he]
  calc
    _ ≤ ∑ i : Fin N, ∑ j : Fin N, ‖conj (x i)*y j*((r i-s i)+(r j-s j))/((i:ℂ)+(j:ℂ)+2)‖ := by
      apply (norm_sum_le _ _).trans
      exact Finset.sum_le_sum (fun i _ => norm_sum_le _ _)
    _ ≤ ∑ i : Fin N, ∑ j : Fin N, ‖x i‖*‖y j‖*ε := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact cross_error_bound i j _ _ _ _ ε hε (hr i) (hr j)
    _ = _ := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring


/-- Truncate the native response itself, at the same physical address. -/
def rhoPrefix (h : ℝ) (i M : ℕ) : ℂ :=
  (-Complex.I / 2) * ((2 * CarryMovingRadial.point h i) *
    ∑ n ∈ Finset.range M, (CarryMovingRadial.point h i ^ 2)^n *
      (canonicalCompletedNativeLogDerivativeMoment n : ℂ))

/-- The existing infinite source-tail certificate applies to every address
of every finite family, without assuming a sign for any Hankel block. -/
theorem native_address_prefix_error (h : ℝ) (i M : ℕ)
    (hz : ‖CarryMovingRadial.point h i‖ < 1/4)
    (hF : completedNativeOperatorCharacteristic (CarryMovingRadial.point h i) ≠ 0) :
    ‖CarryMovingRadial.rho h i - rhoPrefix h i M‖ ≤
      ‖CarryMovingRadial.point h i‖ *
        ((22/175:ℝ)*((22/175:ℝ)*‖CarryMovingRadial.point h i‖^2)^M /
          (1-(22/175:ℝ)*‖CarryMovingRadial.point h i‖^2)) := by
  have hq : completedNativeOperatorLogDerivative (CarryMovingRadial.point h i) =
      2*Complex.I*CarryMovingRadial.rho h i := by
    simpa only [CarryMovingRadial.point, CarryMovingRadial.rho, mul_assoc] using
      CarryRadialFlow.original_rotated_response (((i:ℂ)+1)*(h:ℂ))
  have he : CarryMovingRadial.rho h i - rhoPrefix h i M =
      (-Complex.I / 2) * (completedNativeOperatorLogDerivative (CarryMovingRadial.point h i) -
        (2 * CarryMovingRadial.point h i) *
          ∑ n ∈ Finset.range M, (CarryMovingRadial.point h i ^ 2)^n *
            (canonicalCompletedNativeLogDerivativeMoment n : ℂ)) := by
    unfold rhoPrefix
    rw [hq]
    have hi : Complex.I*Complex.I = -1 := Complex.I_mul_I
    linear_combination (CarryMovingRadial.rho h i) * hi
  rw [he, norm_mul, norm_div, norm_neg, Complex.norm_I]
  norm_num only [Complex.norm_ofNat]
  have hb := CarryEffectiveRadial.native_response_prefix_error (CarryMovingRadial.point h i) hz hF M
  nlinarith


/-- An explicit common bound on the native tail lifts to the complete
polarized pairing for arbitrary finite families. -/
theorem native_family_prefix_error (N M : ℕ) (h ε : ℝ) (x y : Fin N → ℂ)
    (hε : 0 ≤ ε)
    (hz : ∀ i : Fin N, ‖CarryMovingRadial.point h i‖ < 1/4)
    (hF : ∀ i : Fin N, completedNativeOperatorCharacteristic (CarryMovingRadial.point h i) ≠ 0)
    (ht : ∀ i : Fin N, ‖CarryMovingRadial.point h i‖ *
       ((22/175:ℝ)*((22/175:ℝ)*‖CarryMovingRadial.point h i‖^2)^M /
         (1-(22/175:ℝ)*‖CarryMovingRadial.point h i‖^2)) ≤ ε) :
    ‖materialPair N (fun i => CarryMovingRadial.rho h i) x y -
      materialPair N (fun i => rhoPrefix h i M) x y‖ ≤
      ε*(∑ i : Fin N, ‖x i‖)*(∑ j : Fin N, ‖y j‖) := by
  apply material_pair_uniform_error N _ _ x y ε hε
  intro i
  exact (native_address_prefix_error h i M (hz i) (hF i)).trans (ht i)

/-- Every original address is regular when the whole finite grid fits in
the source disc. The grid size is arbitrary, including zero. -/
theorem finite_radial_regular (N : ℕ) (h : ℝ) (hh : (N:ℝ)*|h| < 1/4)
    (j : Fin N) :
    completedNativeOperatorCharacteristic (CarryMovingRadial.point h j) ≠ 0 ∧
    completedNativePositiveHermiteBiehlerCoordinate (CarryMovingRadial.point h j) ≠ 0 := by
  have he : CarryMovingRadial.point h j=Complex.I*((((j:ℝ)+1)*h:ℝ):ℂ) := by
    unfold CarryMovingRadial.point; push_cast; ring
  have hp : |((j:ℝ)+1)*h| < 1/4 := by
    rw [abs_mul,abs_of_nonneg (by positivity : (0:ℝ)≤(j:ℝ)+1)]
    have hj : (j:ℝ)+1≤N := by exact_mod_cast (show (j:ℕ)+1≤N by omega)
    have hb := mul_le_mul_of_nonneg_right hj (abs_nonneg h)
    linarith
  rw [he]
  exact CarryEffectiveRadial.imaginary_radial_regular _ hp


def addressBudget (h : ℝ) (i M : ℕ) : ℝ :=
  ‖CarryMovingRadial.point h i‖ *
    ((22/175:ℝ)*((22/175:ℝ)*‖CarryMovingRadial.point h i‖^2)^M /
      (1-(22/175:ℝ)*‖CarryMovingRadial.point h i‖^2))

def familyBudget (N M : ℕ) (h : ℝ) : ℝ :=
  ∑ i : Fin N, addressBudget h i M

theorem address_budget_nonneg (h : ℝ) (i M : ℕ)
    (hz : ‖CarryMovingRadial.point h i‖ < 1/4) : 0 ≤ addressBudget h i M := by
  unfold addressBudget
  have hn : 0 < 1-(22/175:ℝ)*‖CarryMovingRadial.point h i‖^2 := by
    nlinarith [norm_nonneg (CarryMovingRadial.point h i)]
  positivity

theorem finite_grid_radius (N : ℕ) (h : ℝ) (hh : (N:ℝ)*|h| < 1/4)
    (j : Fin N) : ‖CarryMovingRadial.point h j‖ < 1/4 := by
  have he : CarryMovingRadial.point h j=Complex.I*((((j:ℝ)+1)*h:ℝ):ℂ) := by
    unfold CarryMovingRadial.point; push_cast; ring
  have hp : |((j:ℝ)+1)*h| < 1/4 := by
    rw [abs_mul,abs_of_nonneg (by positivity : (0:ℝ)≤(j:ℝ)+1)]
    have hj : (j:ℝ)+1≤N := by exact_mod_cast (show (j:ℕ)+1≤N by omega)
    have hb := mul_le_mul_of_nonneg_right hj (abs_nonneg h)
    linarith
  rw [he, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  exact hp

/-- Explicit all-order bound, with no unknown tail constant and no
assumption that the original physical form is positive. -/
theorem native_finite_grid_budget (N M : ℕ) (h : ℝ) (x y : Fin N → ℂ)
    (hh : (N:ℝ)*|h| < 1/4) :
    ‖materialPair N (fun i => CarryMovingRadial.rho h i) x y -
      materialPair N (fun i => rhoPrefix h i M) x y‖ ≤
      familyBudget N M h*(∑ i : Fin N, ‖x i‖)*(∑ j : Fin N, ‖y j‖) := by
  have hz (i : Fin N) := finite_grid_radius N h hh i
  have hn (i : Fin N) : 0 ≤ addressBudget h i M := address_budget_nonneg h i M (hz i)
  apply native_family_prefix_error N M h (familyBudget N M h) x y
  · exact Finset.sum_nonneg (fun i _ => hn i)
  · exact hz
  · exact fun i => (finite_radial_regular N h hh i).1
  · intro i
    exact Finset.single_le_sum (fun j _ => hn j) (Finset.mem_univ i)


/-- The estimate is applied only after the full two-leg source has been
synthesized. Its original amplitude and Cauchy crosses remain untouched. -/
theorem full_physical_grid_budget (N M : ℕ) (h : ℝ) (x y : Fin N → ℂ)
    (hpos : 0 < h) (hh : (N:ℝ)*|h| < 1/4) :
    ‖CarryMovingRadial.fullPair N (fun i => CarryMovingRadial.curveQuotient h i)
        (CarryMovingRadial.curveCoefficients N h x) (CarryMovingRadial.curveCoefficients N h y) -
      (2/(h:ℂ))*materialPair N (fun i => rhoPrefix h i M) x y‖ ≤
      (2/h)*(familyBudget N M h*(∑ i : Fin N, ‖x i‖)*(∑ j : Fin N, ‖y j‖)) := by
  rw [CarryMovingRadial.fullPair_eq_response N h (le_of_lt hpos) x y
    (fun i => (finite_radial_regular N h hh i).1)
    (fun i => (finite_radial_regular N h hh i).2)]
  have he : CarryMovingRadial.responsePair N h x y =
      (2/(h:ℂ))*materialPair N (fun i => CarryMovingRadial.rho h i) x y := rfl
  rw [he, ← mul_sub, norm_mul, norm_div, Complex.norm_ofNat, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hpos]
  exact mul_le_mul_of_nonneg_left (native_finite_grid_budget N M h x y hh) (by positivity)


/-- At every fixed physical grid, the explicit full tail budget vanishes as
its source-series truncation order increases. -/
theorem address_budget_tendsto_zero (h : ℝ) (i : ℕ)
    (hz : ‖CarryMovingRadial.point h i‖ < 1/4) :
    Tendsto (fun M : ℕ => addressBudget h i M) atTop (𝓝 0) := by
  have hq : (22/175:ℝ)*‖CarryMovingRadial.point h i‖^2 < 1 := by
    nlinarith [norm_nonneg (CarryMovingRadial.point h i)]
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one
    (show (0:ℝ) ≤ (22/175:ℝ)*‖CarryMovingRadial.point h i‖^2 by positivity) hq
  have hc := ht.const_mul (‖CarryMovingRadial.point h i‖*(22/175:ℝ) /
    (1-(22/175:ℝ)*‖CarryMovingRadial.point h i‖^2))
  simp only [mul_zero] at hc
  convert hc using 1
  ext M
  unfold addressBudget
  ring

theorem family_budget_tendsto_zero (N : ℕ) (h : ℝ) (hh : (N:ℝ)*|h| < 1/4) :
    Tendsto (fun M : ℕ => familyBudget N M h) atTop (𝓝 0) := by
  have ht := tendsto_finsetSum (Finset.univ : Finset (Fin N))
    (fun i _ => address_budget_tendsto_zero h i (finite_grid_radius N h hh i))
  simpa only [familyBudget, Finset.sum_const_zero] using ht

end
end CarryAllOrderTail
