import CubicVectors

namespace CarryGreenCubic
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryCommutatorControl
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryMixedParity CarryCrossRadial CarryGreenLeading NativeLaguerre
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000

/-- Exact diagnostic of each ORIGINAL ordered crossing, after its first
coefficient is identified. The two complete vector errors remain explicit. -/
theorem cubic_crossing_identity (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    ∀ᶠ k : ℕ in atTop, ∀ a b : Fin 3,
      ((k:ℂ)+1)*(partCross eta h0 h1 a b k-((k:ℂ)+1)*leadingCoefficient eta h0 h1 a b)=
        (Real.sqrt 2:ℂ)*
          ((1/4:ℂ)*inner ℂ (constantPart eta h0 h1 (nativeEvenProfile 0) a)
            (cubicPart eta h0 h1 (nativeOddProfile 0) b (2*k+1))+
           2*inner ℂ (cubicPart eta h0 h1 (nativeEvenProfile 0) a k)
            (constantPart eta h0 h1 (nativeOddProfile 0) b)) := by
  filter_upwards [part_cross_scaled_identity eta h0 h1] with k hk
  intro a b
  have he := hk a b
  unfold cubicPart leadingCoefficient
  simp only [inner_sub_left,inner_sub_right,inner_smul_left,inner_smul_right,
    map_pow,map_add,map_natCast,map_one,Complex.conj_ofReal]
  push_cast
  have hi : ((k:ℂ)+1)*(radialStep k:ℂ)=1 := by
    unfold radialStep; push_cast
    exact mul_inv_cancel₀ (by exact_mod_cast (show k+1≠0 by omega))
  linear_combination ((k:ℂ)+1)^2*he-((k:ℂ)+1)*partCross eta h0 h1 a b k*hi

/-- Cubic coefficient in the SAME complete two-input physical form. -/
def cubicCoefficient (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) (a b : Fin 3) : ℂ :=
  -(Real.sqrt 2:ℂ)*(h 1:ℂ)*
    ((1/4:ℂ)*inner ℂ (constantPart eta h0 h1 (nativeEvenProfile 0) a)
      (cubicProfile eta h0 h1 (nativeOddProfile 0) b)+
     2*inner ℂ (cubicProfile eta h0 h1 (nativeEvenProfile 0) a)
      (constantPart eta h0 h1 (nativeOddProfile 0) b))

/-- The proposed law is proved for ALL NINE ordered physical components. -/
theorem cubic_crossing_tendsto (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) (a b : Fin 3) :
    Tendsto (fun k : ℕ => ((k:ℂ)+1)*
      (partCross eta h0 h1 a b k-((k:ℂ)+1)*leadingCoefficient eta h0 h1 a b))
      atTop (nhds (cubicCoefficient eta h0 h1 a b)) := by
  have ho := (cubic_part_tendsto eta h0 h1 (nativeOddProfile 0) b).comp doubled_index_tendsto
  have he := cubic_part_tendsto eta h0 h1 (nativeEvenProfile 0) a
  have hl := (tendsto_const_nhds (x:=(Real.sqrt 2:ℂ))).mul
    ((((tendsto_const_nhds (x:=constantPart eta h0 h1 (nativeEvenProfile 0) a)).inner ho).const_mul (1/4:ℂ)).add
      ((he.inner (tendsto_const_nhds (x:=constantPart eta h0 h1 (nativeOddProfile 0) b))).const_mul 2))
  have hval : (Real.sqrt 2:ℂ)*
      ((1/4:ℂ)*inner ℂ (constantPart eta h0 h1 (nativeEvenProfile 0) a)
        ((-(h 1:ℂ)) • cubicProfile eta h0 h1 (nativeOddProfile 0) b)+
       2*inner ℂ ((-(h 1:ℂ)) • cubicProfile eta h0 h1 (nativeEvenProfile 0) a)
        (constantPart eta h0 h1 (nativeOddProfile 0) b))=cubicCoefficient eta h0 h1 a b := by
    simp only [inner_smul_left,inner_smul_right,map_neg,Complex.conj_ofReal,cubicCoefficient]
    ring
  rw [hval] at hl
  apply hl.congr'
  filter_upwards [cubic_crossing_identity eta h0 h1] with k hk
  exact (hk a b).symm

theorem cubic_residual_residual_zero (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    cubicCoefficient eta h0 h1 2 2=0 := by
  simp only [cubicCoefficient,constantPart,part_constant_residual_zero,
    inner_zero_left,inner_zero_right,mul_zero,zero_add]

theorem cubic_residual_row (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) (b : Fin 3) :
    cubicCoefficient eta h0 h1 2 b=
      -2*(Real.sqrt 2:ℂ)*(h 1:ℂ)*inner ℂ
        (cubicProfile eta h0 h1 (nativeEvenProfile 0) 2)
        (constantPart eta h0 h1 (nativeOddProfile 0) b) := by
  simp only [cubicCoefficient,constantPart,part_constant_residual_zero,
    inner_zero_left,mul_zero,zero_add]
  ring

theorem cubic_residual_column (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) (a : Fin 3) :
    cubicCoefficient eta h0 h1 a 2=
      -(Real.sqrt 2:ℂ)*(h 1:ℂ)/4*inner ℂ
        (constantPart eta h0 h1 (nativeEvenProfile 0) a)
        (cubicProfile eta h0 h1 (nativeOddProfile 0) 2) := by
  simp only [cubicCoefficient,constantPart,part_constant_residual_zero,
    inner_zero_right,mul_zero,add_zero]
  ring

end
end CarryGreenCubic
