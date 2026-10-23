import SourceMap
import SchurTransport
import LiteralNativeTrace

namespace CarrySourceBezout
open CarrySelfAdjointOperator NativeTrace
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 1600000

/-- Literal jets of the original completed TFVD head; no parity imposed. -/
def literalHead (M : ℕ) (n : ℕ) : ℂ :=
  sourceJet (2*n) (fun z => (headTrace M z).1)

/-- Literal completed tail, including original Xi/chart and boundary terms. -/
def literalTail (M : ℕ) (n : ℕ) : ℂ :=
  sourceJet (2*n) (fun z => (tailTrace M z).1)

theorem literal_head_tail (M : ℕ) :
    (fun n => (nativeC n : ℂ)) = literalHead M + literalTail M := by
  funext n
  rw [← completedNativeEvenCharacteristicCoefficient_eq_real,
    ← completedNativeFullCharacteristicTaylorCoefficient_even]
  change sourceJet (2*n) completedNativeOperatorCharacteristic = _
  unfold sourceJet
  rw [(full_value_eventually_head_tail M).iteratedDeriv_eq]
  exact sourceJet_add _ _ _ (head_value_analytic M) (tail_value_analytic M)

def complexPair {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (x y : Fin n → ℂ) : ℂ := x ⬝ᵥ (A *ᵥ y)

theorem complexPair_add {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (x y : Fin n → ℂ) :
    complexPair (A+B) x y = complexPair A x y + complexPair B x y := by
  simp [complexPair, Matrix.add_mulVec, dotProduct_add]

theorem coefficientBlock_add (a b : BiSeries ℂ) (r : ℕ) :
    coefficientBlock (a+b) r = coefficientBlock a r + coefficientBlock b r := by
  ext i j
  simp [coefficientBlock]

theorem complexPair_real {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (x y : Fin n → ℝ) :
    complexPair (A.map Complex.ofRealHom) (fun i => (x i : ℂ)) (fun j => (y j : ℂ)) =
      (matrixPair A x y : ℂ) := by
  simp [complexPair, matrixPair, Matrix.mulVec, dotProduct, Complex.ofReal_sum,
    Complex.ofReal_mul]

def literalTerm (M P : ℕ) (headLeft headRight : Bool) (b : Bool) (r : ℕ)
    (x y : Fin r → ℝ) : ℂ :=
  complexPair (coefficientBlock (mixedSourceKernel
    (if headLeft then literalHead M else literalTail M)
    (if headRight then literalHead P else literalTail P) b) r)
    (fun i => (x i : ℂ)) (fun j => (y j : ℂ))

/-- Both independent cutoffs and inputs survive all four ordered terms. -/
theorem literal_four_terms (M P : ℕ) (b : Bool) (r : ℕ) (x y : Fin r → ℝ) :
    (matrixPair (coefficientBlock (sourceKernel nativeC b) r) x y : ℂ) =
      literalTerm M P true true b r x y + literalTerm M P true false b r x y +
      literalTerm M P false true b r x y + literalTerm M P false false b r x y := by
  have he : sourceKernel (fun n => (nativeC n : ℂ)) b =
      mixedSourceKernel (literalHead M) (literalHead P) b +
      mixedSourceKernel (literalHead M) (literalTail P) b +
      mixedSourceKernel (literalTail M) (literalHead P) b +
      mixedSourceKernel (literalTail M) (literalTail P) b := by
    change mixedSourceKernel (fun n => (nativeC n : ℂ)) (fun n => (nativeC n : ℂ)) b = _
    conv_lhs => arg 1; rw [literal_head_tail M]
    conv_lhs => arg 2; rw [literal_head_tail P]
    rw [mixedSourceKernel_add_left, mixedSourceKernel_add_right,
      mixedSourceKernel_add_right]
    abel
  have hm := sourceKernel_map Complex.ofRealHom nativeC b
  change sourceKernel (fun n => (nativeC n : ℂ)) b = _ at hm
  rw [hm] at he
  have hblock := congrArg (fun f : BiSeries ℂ => coefficientBlock f r) he
  rw [coefficientBlock_map] at hblock
  simp only [coefficientBlock_add] at hblock
  rw [← complexPair_real, hblock]
  simp [complexPair_add, literalTerm]

def literalResidualTerm (M P : ℕ) (a d : Bool) (b : Bool) (n : ℕ) : ℂ :=
  literalTerm M P a d b (n+1)
    (monicSourceDirection nativeC nativeH (if b then 1 else 0) n)
    (monicSourceDirection nativeC nativeH (if b then 1 else 0) n)

/-- Same PR41 residual, no signs assumed, no separate real projections. -/
theorem native_residual_literal_four_terms (M P : ℕ) (b : Bool) (n : ℕ)
    (hA : IsUnit (sourceMomentMatrix nativeH (if b then 1 else 0) n)) :
    literalResidualTerm M P true true b n + literalResidualTerm M P true false b n +
      literalResidualTerm M P false true b n + literalResidualTerm M P false false b n =
      (nativeC 0 * nativeSourceSchurRemainder (if b then 1 else 0) n : ℝ) := by
  unfold literalResidualTerm
  rw [← literal_four_terms]
  exact congrArg Complex.ofReal (native_monicSourceDirection_remainder b n hA)

end
end CarrySourceBezout
