import NativeProductFactor

/-!
# Transporte polarizado da fatoração literal para o resíduo de Schur

As duas variáveis e o termo corretivo são mantidos, sem positividade assumida.
A cota provada é para a diferença completa em relação ao bloco da cabeça;
não se atribui sinal ou convergência separada a cada parcela do produto.
-/
namespace CarrySourceBezout
open CarrySelfAdjointOperator NativeTrace Filter Matrix
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000

def literalProductHeadBlock (M : ℕ) (b : Bool) (r : ℕ) : Matrix (Fin r) (Fin r) ℂ :=
  convolutionMatrix (literalCorrection M) r * coefficientBlock (sourceKernel (literalHead M) b) r *
    (convolutionMatrix (literalCorrection M) r).transpose

def literalProductCorrectionBlock (M : ℕ) (b : Bool) (r : ℕ) : Matrix (Fin r) (Fin r) ℂ :=
  convolutionMatrix (literalHead M) r * coefficientBlock (sourceKernel (literalCorrection M) b) r *
    (convolutionMatrix (literalHead M) r).transpose

theorem literal_product_blocks (M : ℕ) (hM : literalHead M 0 ≠ 0) (b : Bool) (r : ℕ) :
    (coefficientBlock (sourceKernel nativeC b) r).map Complex.ofRealHom =
      literalProductHeadBlock M b r + literalProductCorrectionBlock M b r := by
  have hf := sourceKernel_product_block (literalHead M) (literalCorrection M) b r
  rw [literal_product_coefficients M hM] at hf
  have hm := sourceKernel_map Complex.ofRealHom nativeC b
  change sourceKernel (fun n => (nativeC n : ℂ)) b = _ at hm
  rw [hm, coefficientBlock_map] at hf
  exact hf

theorem literal_product_pair (M : ℕ) (hM : literalHead M 0 ≠ 0) (b : Bool) (r : ℕ)
    (x y : Fin r → ℝ) :
    (matrixPair (coefficientBlock (sourceKernel nativeC b) r) x y : ℂ) =
      complexPair (literalProductHeadBlock M b r) (fun i => (x i:ℂ)) (fun i => (y i:ℂ)) +
      complexPair (literalProductCorrectionBlock M b r) (fun i => (x i:ℂ)) (fun i => (y i:ℂ)) := by
  rw [← complexPair_real, literal_product_blocks M hM, complexPair_add]

theorem literal_product_critical (M : ℕ) (hM : literalHead M 0 ≠ 0) (b : Bool) (n : ℕ)
    (hA : IsUnit (sourceMomentMatrix nativeH (if b then 1 else 0) n)) :
    let v := monicSourceDirection nativeC nativeH (if b then 1 else 0) n
    complexPair (literalProductHeadBlock M b (n+1)) (fun i => (v i:ℂ)) (fun i => (v i:ℂ)) +
      complexPair (literalProductCorrectionBlock M b (n+1)) (fun i => (v i:ℂ)) (fun i => (v i:ℂ)) =
        (nativeC 0 * nativeSourceSchurRemainder (if b then 1 else 0) n : ℝ) := by
  dsimp only
  rw [← literal_product_pair M hM]
  exact congrArg Complex.ofReal (native_monicSourceDirection_remainder b n hA)

def literalProductDifference (M : ℕ) (b : Bool) (r : ℕ) (x y : Fin r → ℝ) : ℂ :=
  complexPair (literalProductHeadBlock M b r) (fun i => (x i:ℂ)) (fun i => (y i:ℂ)) +
    complexPair (literalProductCorrectionBlock M b r) (fun i => (x i:ℂ)) (fun i => (y i:ℂ)) -
      literalTerm M M true true b r x y

/-- The product correction equals the three original ordered tail crossings. -/
theorem literal_product_difference_eq_mixed (M : ℕ) (hM : literalHead M 0 ≠ 0)
    (b : Bool) (r : ℕ) (x y : Fin r → ℝ) :
    literalProductDifference M b r x y =
      literalTerm M M true false b r x y + literalTerm M M false true b r x y +
        literalTerm M M false false b r x y := by
  unfold literalProductDifference
  rw [← literal_product_pair M hM, literal_four_terms]
  ring

theorem literal_product_difference_bound (M : ℕ) (hM : literalHead M 0 ≠ 0)
    (b : Bool) (r : ℕ) (x y : Fin r → ℝ) :
    ‖literalProductDifference M b r x y‖ ≤ literalErrorBudget M M b r x y := by
  unfold literalProductDifference
  rw [← literal_product_pair M hM]
  exact literal_error_bound M M b r x y

theorem literal_product_difference_tendsto_zero (b : Bool) (r : ℕ) (x y : Fin r → ℝ) :
    Tendsto (fun M => literalProductDifference M b r x y) atTop (nhds 0) := by
  apply squeeze_zero_norm' ?_ (literal_error_budget_tendsto_zero b r x y)
  filter_upwards [literal_head_constant_eventually_ne] with M hM
  exact literal_product_difference_bound M hM b r x y

#print axioms literal_product_blocks
#print axioms literal_product_pair
#print axioms literal_product_critical
#print axioms literal_product_difference_eq_mixed
#print axioms literal_product_difference_bound
#print axioms literal_product_difference_tendsto_zero
end
end CarrySourceBezout
