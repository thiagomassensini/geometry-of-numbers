import SigmaHeight50Integration

/-!
# Eventual negativity of the original sigma Padé minors

The certified height-50 isolation gives a two-pole leading term for the original
`completedSigmaLogJet`. The exponential remainder stays in the normalized-minor limit, whose
strictly negative determinant limit implies eventual negativity of the original `sigmaPadeD`.
-/

namespace CarrySigmaObstruction

open Filter Topology
open CarrySigmaPade

noncomputable section
set_option autoImplicit false

/-- The certified off-critical zero pair forces every sufficiently late original sigma Padé
minor to be negative. The moments in `sigmaPadeD` remain `completedSigmaLogJet`; the exponentially
small zero-pair remainder is retained in the normalized-minor limit. -/
theorem exists_eventually_negative_sigmaPadeD_from_height50_certificate :
    ∃ P : ℕ, ∀ p ≥ P, sigmaPadeD (1 / 5) p < 0 := by
  obtain ⟨γ, _hγbox, hisolation⟩ :=
    exists_firstSigmaDisplacedProductIsolation_from_height50_certificate
  let d : ℝ := 1 / 5
  let τ : ℂ := (γ : ℂ) + Complex.I * (d : ℂ)
  let ζ : ℂ := τ ^ (-2 : ℤ)
  let R : ℝ := γ ^ 2 + d ^ 2
  let a : ℝ := R⁻¹
  let θ : ℂ := (R : ℂ) * inverseSquareNode γ d
  let x : ℝ := θ.re
  let y : ℝ := θ.im
  have hγ : 0 < γ := hisolation.height_pos
  have hd : 0 < d := hisolation.displacement_pos
  have hR : 0 < R := by dsimp [R]; positivity
  have hτnode : τ = (γ : ℂ) + (d : ℂ) * Complex.I := by
    dsimp [τ]
    ring
  have hζnode : ζ = inverseSquareNode γ d := by
    dsimp [ζ]
    rw [hτnode]
    simp [inverseSquareNode, zpow_neg, inv_pow]
    rfl
  have hθunit : Complex.normSq θ = 1 := by
    change Complex.normSq ((R : ℂ) * inverseSquareNode γ d) = 1
    rw [Complex.normSq_mul, Complex.normSq_ofReal, inverseSquareNode_normSq γ d hγ]
    dsimp [R]
    field_simp
  have hθim : θ.im = -(2 * γ * d) / R := by
    change ((R : ℂ) * inverseSquareNode γ d).im = _
    rw [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re]
    simp only [zero_mul, add_zero]
    rw [inverseSquareNode_im γ d hγ]
    dsimp [R]
    field_simp [ne_of_gt hR]
  have hy : y < 0 := by
    dsimp [y]
    rw [hθim]
    have hnum : 0 < 2 * γ * d := by positivity
    exact div_neg_of_neg_of_pos (neg_neg_of_pos hnum) hR
  have ha : 0 < a := by dsimp [a]; exact inv_pos.mpr hR
  have hζfactor : ζ = (a : ℂ) * θ := by
    have haR : a * R = 1 := by dsimp [a]; field_simp [ne_of_gt hR]
    calc
      ζ = (1 : ℂ) * inverseSquareNode γ d := by rw [hζnode]; simp
      _ = ((a * R : ℝ) : ℂ) * inverseSquareNode γ d := by rw [haR]; simp
      _ = (a : ℂ) * ((R : ℂ) * inverseSquareNode γ d) := by push_cast; ring
  have hre : θ.re = x := rfl
  have him : θ.im = y := rfl
  have hnormθsq : ‖θ‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq θ]
    exact hθunit
  have hnormθ : ‖θ‖ = 1 := by
    have hnonneg := norm_nonneg θ
    nlinarith
  have hnormζ : ‖ζ‖ = a := by
    rw [hζfactor, norm_mul, hnormθ]
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
  obtain ⟨C, η, hC, hη, hηζ, _hsource, hbound⟩ :=
    completedNative_sigmaRemainder_square_decomposition_of_isolation
      d γ (Real.sqrt 300) 1 hisolation
  have hboundζ : ∀ n, |sigmaZeroPairRemainderMoment d 1 ζ n| ≤ C * η ^ n := by
    simpa [ζ, τ] using hbound
  have hηa : η < a := by
    have hηζ' : η < ‖ζ‖ := by simpa [ζ, τ] using hηζ
    rw [← hnormζ]
    exact hηζ'
  have hminors := sigmaPadeNormalizedMinors_tendsto_of_unitCircle_twoPole_remainder
    d 1 a C η x y ζ θ hζfactor hre him hθunit (le_of_lt hη) ha hηa hboundζ
  have hyne : y ≠ 0 := ne_of_lt hy
  have hD₀ : -(1 : ℝ) ^ 2 * y ^ 2 < 0 := by
    nlinarith [sq_pos_of_ne_zero hyne]
  have hDneg := sigmaPadeD_eventually_neg_of_normalized_limit
    d a (-(1 : ℝ) ^ 2 * y ^ 2) hminors.1 ha hD₀
  obtain ⟨P, hP⟩ := Filter.eventually_atTop.mp hDneg
  exact ⟨P, fun p hp => hP p hp⟩

end
end CarrySigmaObstruction

#print axioms CarrySigmaObstruction.exists_eventually_negative_sigmaPadeD_from_height50_certificate
