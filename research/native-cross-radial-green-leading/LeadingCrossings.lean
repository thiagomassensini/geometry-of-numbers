import RadialPartExpansion

namespace CarryGreenLeading
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryCommutatorControl CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryMixedParity CarryCrossRadial NativeLaguerre
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000

theorem chiral_difference_square : conj chiralDifference*chiralDifference=2 := by
  have hs : (Real.sqrt 2:ℂ)^2=2 := by
    rw [← Complex.ofReal_pow,Real.sq_sqrt (by norm_num)]; norm_num
  have hn : (Real.sqrt 2:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne'
  calc
    _ = 4/(Real.sqrt 2:ℂ)^2 := by
      simp only [chiralDifference,map_div₀,map_mul,map_ofNat,Complex.conj_I,Complex.conj_ofReal]
      field_simp [hn]
      ring_nf
      norm_num [Complex.I_sq]
    _ = 2 := by rw [hs]; norm_num

/-- All nine complete ordered pairings are extracted from the already proved
VECTORS; two independently regularized native responses remain distinct. -/
theorem native_parts_pair {α : Type*} {f : Filter α} (u v : α → ℕ)
    (hu : Tendsto u f atTop) (hv : Tendsto v f atTop)
    (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) (c d : ℕ →₀ ℂ) :
    ∀ᶠ x in f, ∀ a b : Fin 3,
      canonicalCompletedNativeProjectiveChiralForm
        (completedSourceParts eta h0 h1 (u x) c a) (completedSourceParts eta h0 h1 (v x) d b)=
      (crossScale (u x) (v x):ℂ)*
        (inner ℂ (constantPart eta h0 h1 c a)
          (partField eta h0 h1 (responseSamples (radialStep (v x))) d b)+
         inner ℂ (partField eta h0 h1 (responseSamples (radialStep (u x))) c a)
          (constantPart eta h0 h1 d b)) := by
  filter_upwards [hu.eventually (native_part_contrast_mean eta h0 h1 c),
    hv.eventually (native_part_contrast_mean eta h0 h1 d)] with x hc hd
  intro a b
  have he := signed_mean_contrast (completedSourceParts eta h0 h1 (u x) c a)
    (completedSourceParts eta h0 h1 (v x) d b)
  rw [(hc a).1,(hc a).2,(hd b).1,(hd b).2] at he
  simp only [inner_smul_left,inner_smul_right] at he
  have hs : conj ((Real.sqrt ((u x:ℝ)+1):ℂ)*chiralDifference)*
      ((Real.sqrt ((v x:ℝ)+1):ℂ)*chiralDifference)=2*(crossScale (u x) (v x):ℂ) := by
    simp only [map_mul,Complex.conj_ofReal]
    unfold crossScale
    push_cast
    linear_combination ((Real.sqrt ((u x:ℝ)+1):ℂ)*(Real.sqrt ((v x:ℝ)+1):ℂ))*chiral_difference_square
  linear_combination he+(1/2:ℂ)*
    (inner ℂ (constantPart eta h0 h1 c a) (partField eta h0 h1 (responseSamples (radialStep (v x))) d b)+
     inner ℂ (partField eta h0 h1 (responseSamples (radialStep (u x))) c a) (constantPart eta h0 h1 d b))*hs

/-- The actual J0(k),J1(2k+1) source parts, without changing their weights. -/
def partCross (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) (a b : Fin 3) (k : ℕ) : ℂ :=
  canonicalCompletedNativeProjectiveChiralForm
    (completedSourceParts eta h0 h1 k (radialJetCoefficients k 0) a)
    (completedSourceParts eta h0 h1 (2*k+1) (radialJetCoefficients (2*k+1) 1) b)

theorem part_cross_exact (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    ∀ᶠ k : ℕ in atTop, ∀ a b : Fin 3, partCross eta h0 h1 a b k=
      2*(Real.sqrt 2:ℂ)*((k:ℂ)+1)^2*
        (inner ℂ (constantPart eta h0 h1 (nativeEvenProfile 0) a)
          (partField eta h0 h1 (responseSamples (radialStep (2*k+1))) (nativeOddProfile 0) b)+
         inner ℂ (partField eta h0 h1 (responseSamples (radialStep k)) (nativeEvenProfile 0) a)
          (constantPart eta h0 h1 (nativeOddProfile 0) b)) := by
  filter_upwards [native_parts_pair (fun k : ℕ => k) (fun k => 2*k+1)
    tendsto_id doubled_index_tendsto eta h0 h1 (nativeEvenProfile 0) (nativeOddProfile 0)] with k hk
  intro a b
  unfold partCross
  rw [radial_even_calibration k 0,radial_odd_calibration (2*k+1) 0]
  norm_num only [Nat.mul_zero,zero_add,pow_zero,pow_one,one_smul]
  rw [completed_part_scale_input]
  simp only [canonicalCompletedNativeProjectiveChiralForm,Prod.smul_fst,Prod.smul_snd,
    inner_smul_right]
  have he := hk a b
  unfold canonicalCompletedNativeProjectiveChiralForm at he
  rw [doubled_cross_scale] at he
  push_cast at he ⊢
  linear_combination (2*(k:ℂ)+2)*he

/-- Exact normalized observation of every original ordered pairing, with both
normalized VECTOR fields still explicit. -/
theorem part_cross_scaled_identity (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    ∀ᶠ k : ℕ in atTop, ∀ a b : Fin 3, (radialStep k:ℂ)*partCross eta h0 h1 a b k=
      (Real.sqrt 2:ℂ)*
        (inner ℂ (constantPart eta h0 h1 (nativeEvenProfile 0) a)
          (normalizedPart eta h0 h1 (nativeOddProfile 0) b (2*k+1))+
         2*inner ℂ (normalizedPart eta h0 h1 (nativeEvenProfile 0) a k)
          (constantPart eta h0 h1 (nativeOddProfile 0) b)) := by
  filter_upwards [part_cross_exact eta h0 h1] with k hk
  intro a b
  rw [hk a b]
  unfold normalizedPart
  simp only [inner_smul_left,inner_smul_right,map_add,map_natCast,map_one]
  push_cast
  have hi : ((k:ℂ)+1)*(radialStep k:ℂ)=1 := by
    unfold radialStep; push_cast
    exact mul_inv_cancel₀ (by exact_mod_cast (show k+1≠0 by omega))
  linear_combination 2*(Real.sqrt 2:ℂ)*((k:ℂ)+1)*
    (inner ℂ (constantPart eta h0 h1 (nativeEvenProfile 0) a)
      (partField eta h0 h1 (responseSamples (radialStep (2*k+1))) (nativeOddProfile 0) b)+
     inner ℂ (partField eta h0 h1 (responseSamples (radialStep k)) (nativeEvenProfile 0) a)
      (constantPart eta h0 h1 (nativeOddProfile 0) b))*hi

/-- Explicit nine coefficients made from the ORIGINAL fixed physical vectors. -/
def leadingCoefficient (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) (a b : Fin 3) : ℂ :=
  (Real.sqrt 2:ℂ)*(h 0:ℂ)*
    (inner ℂ (constantPart eta h0 h1 (nativeEvenProfile 0) a)
      (linearPart eta h0 h1 (nativeOddProfile 0) b)+
     2*inner ℂ (linearPart eta h0 h1 (nativeEvenProfile 0) a)
      (constantPart eta h0 h1 (nativeOddProfile 0) b))

theorem part_cross_scaled_tendsto (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) (a b : Fin 3) :
    Tendsto (fun k : ℕ => (radialStep k:ℂ)*partCross eta h0 h1 a b k) atTop
      (nhds (leadingCoefficient eta h0 h1 a b)) := by
  have ho := (normalized_part_tendsto eta h0 h1 (nativeOddProfile 0) b).comp doubled_index_tendsto
  have he := normalized_part_tendsto eta h0 h1 (nativeEvenProfile 0) a
  have hl := (tendsto_const_nhds (x:=(Real.sqrt 2:ℂ))).mul
    (((tendsto_const_nhds (x:=constantPart eta h0 h1 (nativeEvenProfile 0) a)).inner ho).add
      ((he.inner (tendsto_const_nhds (x:=constantPart eta h0 h1 (nativeOddProfile 0) b))).const_mul 2))
  have hval : (Real.sqrt 2:ℂ)*
      (inner ℂ (constantPart eta h0 h1 (nativeEvenProfile 0) a)
        ((h 0:ℂ) • linearPart eta h0 h1 (nativeOddProfile 0) b)+
       2*inner ℂ ((h 0:ℂ) • linearPart eta h0 h1 (nativeEvenProfile 0) a)
        (constantPart eta h0 h1 (nativeOddProfile 0) b))=leadingCoefficient eta h0 h1 a b := by
    simp only [inner_smul_left,inner_smul_right,Complex.conj_ofReal,leadingCoefficient]
    ring
  rw [hval] at hl
  apply hl.congr'
  filter_upwards [part_cross_scaled_identity eta h0 h1] with k hk
  exact (hk a b).symm

end
end CarryGreenLeading
