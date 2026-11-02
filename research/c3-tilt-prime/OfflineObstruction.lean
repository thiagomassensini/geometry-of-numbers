import TiltSourceGate

/-!
# Fase A — Obstrução de positividade fora da linha autodual (esqueleto condicional)

Inverte a carga da prova. Em vez de forçar positividade na linha (o crux da #145),
isola o **único** passo geométrico restante como hipótese `c₅ ≥ limiar` (resp. `c₆`)
e prova que ele é **incompatível** com a positividade genuína do pivô de Schur.

Dois pilares já formalizados fecham a lógica:
* positividade genuína: `canonicalGreenJetHankelGramPosDef` ⟹ `0 < sourceMomentSchur`
  (o pivô genuíno é estritamente positivo);
* gate: `even_source_sign_iff` / `even_pivot_gate_carrier`
  (`0 < pivô ↔ c₅ < limiar/(5c₀)`).

Portanto `c₅ ≥ limiar/(5c₀)` ⟹ pivô ≤ 0 ⟹ a configuração **não** é genuína.
A obrigação `c₅(σ) ≥ limiar(σ)` para `σ ≠ 1/2` é a Fase B (a negatividade geométrica).

Não modifica nenhum módulo anterior.
-/

namespace CarryTiltSlice
open CPFormal.Analytic.Cp CarrySelfAdjointOperator CarrySourceBezout CarrySourceDimensionThree
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

/-! ## Obstrução algébrica para uma fonte arbitrária -/

/-- Positividade do pivô par é incompatível com `c₅` no (ou acima do) limiar. -/
theorem even_pivot_obstruction (c : ℕ → ℝ) (hc : 0 < c 0)
    (hpos : 0 < sourceSchur c false 2)
    (hceil : evenSourceCeiling c / (5 * c 0) ≤ c 5) : False := by
  have hlt := (even_source_sign_iff c hc).mp hpos
  linarith

/-- Positividade do pivô ímpar é incompatível com `c₆` no (ou acima do) limiar. -/
theorem odd_pivot_obstruction (c : ℕ → ℝ) (hc : 0 < c 0)
    (hpos : 0 < sourceSchur c true 2)
    (hceil : oddSourceCeiling c / (6 * c 0) ≤ c 6) : False := by
  have hlt := (odd_source_sign_iff c hc).mp hpos
  linarith

/-- Fora da linha (`c₅` no ou acima do limiar) o pivô par é não positivo. -/
theorem even_superceiling_pivot_nonpos (c : ℕ → ℝ) (hc : 0 < c 0)
    (hceil : evenSourceCeiling c / (5 * c 0) ≤ c 5) :
    sourceSchur c false 2 ≤ 0 := by
  by_contra h
  exact even_pivot_obstruction c hc (not_le.mp h) hceil

/-- Fora da linha (`c₆` no ou acima do limiar) o pivô ímpar é não positivo. -/
theorem odd_superceiling_pivot_nonpos (c : ℕ → ℝ) (hc : 0 < c 0)
    (hceil : oddSourceCeiling c / (6 * c 0) ≤ c 6) :
    sourceSchur c true 2 ≤ 0 := by
  by_contra h
  exact odd_pivot_obstruction c hc (not_le.mp h) hceil

/-- Positividade genuína força o regime sub-limiar (par). -/
theorem even_genuine_forces_subceiling (c : ℕ → ℝ) (hc : 0 < c 0)
    (hpos : 0 < sourceSchur c false 2) :
    c 5 < evenSourceCeiling c / (5 * c 0) :=
  (even_source_sign_iff c hc).mp hpos

/-- Positividade genuína força o regime sub-limiar (ímpar). -/
theorem odd_genuine_forces_subceiling (c : ℕ → ℝ) (hc : 0 < c 0)
    (hpos : 0 < sourceSchur c true 2) :
    c 6 < oddSourceCeiling c / (6 * c 0) :=
  (odd_source_sign_iff c hc).mp hpos

#print axioms even_pivot_obstruction
#print axioms odd_pivot_obstruction
#print axioms even_superceiling_pivot_nonpos

/-! ## Especialização à fonte nativa (pivô dos momentos genuínos) -/

/-- Obstrução nativa par: o pivô genuíno dos momentos não pode ser positivo se o
quinto coeficiente da fonte completada atinge o limiar. -/
theorem native_even_offline_obstruction (M : ℕ)
    (hA : IsUnit (sourceMomentMatrix nativeH 0 2))
    (hpos : 0 < sourceMomentSchur nativeH 0 2)
    (hceil : evenSourceCeiling (carrierCoefficient M) / (5 * carrierCoefficient M 0)
      ≤ carrierCoefficient M 5) : False := by
  have hlt := (even_pivot_gate_carrier M hA).mp hpos
  linarith

/-- Obstrução nativa ímpar. -/
theorem native_odd_offline_obstruction (M : ℕ)
    (hA : IsUnit (sourceMomentMatrix nativeH 1 2))
    (hpos : 0 < sourceMomentSchur nativeH 1 2)
    (hceil : oddSourceCeiling (carrierCoefficient M) / (6 * carrierCoefficient M 0)
      ≤ carrierCoefficient M 6) : False := by
  have hlt := (odd_pivot_gate_carrier M hA).mp hpos
  linarith

/-- Positividade genuína dos momentos força o quinto coeficiente completado abaixo do limiar. -/
theorem native_even_genuine_forces_subceiling (M : ℕ)
    (hA : IsUnit (sourceMomentMatrix nativeH 0 2))
    (hpos : 0 < sourceMomentSchur nativeH 0 2) :
    carrierCoefficient M 5 < evenSourceCeiling (carrierCoefficient M) / (5 * carrierCoefficient M 0) :=
  (even_pivot_gate_carrier M hA).mp hpos

/-- Positividade genuína dos momentos força o sexto coeficiente completado abaixo do limiar. -/
theorem native_odd_genuine_forces_subceiling (M : ℕ)
    (hA : IsUnit (sourceMomentMatrix nativeH 1 2))
    (hpos : 0 < sourceMomentSchur nativeH 1 2) :
    carrierCoefficient M 6 < oddSourceCeiling (carrierCoefficient M) / (6 * carrierCoefficient M 0) :=
  (odd_pivot_gate_carrier M hA).mp hpos

#print axioms native_even_offline_obstruction
#print axioms native_odd_offline_obstruction

end
end CarryTiltSlice
