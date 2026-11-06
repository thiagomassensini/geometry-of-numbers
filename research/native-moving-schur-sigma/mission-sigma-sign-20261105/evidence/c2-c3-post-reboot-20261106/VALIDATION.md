# Revalidação focada C2/C3 após reinício

**Data:** 2026-11-06
**Base de fontes:** origin/main em 935911bce2c253ee508a4990face113ea63c87ee (PR #202).
**Estado:** C2 e C3 já estavam integrados; esta execução recompilou seus módulos finais e repetiu as auditorias sobre as fontes presentes nessa revisão.

## Resultado

- SigmaPadeEventualNegativity.lean compilou com -DwarningAsError=true. O checker local aceitou o root exists_eventually_negative_sigmaPadeD_from_height50_certificate com apenas propext, Classical.choice e Quot.sound.
- SigmaParityNegativeDirection.lean compilou com -DwarningAsError=true. O checker aceitou os quatro roots C3 com apenas os mesmos três axiomas padrão.
- SigmaPadeAudit.lean compilou com sucesso sobre os dois módulos recém-compilados. A auditoria percorreu 133 roots públicos e 70.861 dependências transitivas de tipo/corpo, confirmou somente axiomas padrão e manteve a proveniência da característica e dos jets sigma originais.
- Os comandos registrados nos logs usaram Lean 4.32.0, Mathlib 81a5d257c8e410db227a6665ed08f64fea08e997, GreenFrame cd2d838bee67ad23f869a02f8ed9f0a0feb926fa e Carry 045369f6dedcb2e75e9aefed1d12c9f73b9a2532.
- A recompilação dos três módulos foi focada em outputs separados e reutilizou os caches de dependências do checkpoint 4.32 em geometry-of-numbers-sigma-c2-c3-main@67aea3263426cc8f9787f34aa7833a5650dde175. Ela não substitui os logs da reconstrução completa e limpa, preservados em ../c3-parity/.

## Proveniência

Os hashes de SigmaPadeEventualNegativity.lean e SigmaParityNegativeDirection.lean conferem com as fontes no commit conferido. A composição de C2 segue usando os momentos originais completedSigmaLogJet e sigmaPadeD e conserva o resto exponencial. A junção de C1/C2 mantém uma única definição de CarrySigmaObstruction.sigmaLineZero, em SigmaCertifiedNegativeDirection.lean, reutilizada por SigmaRHHeightBridge.lean.

Os logs de compilação e auditoria estão neste diretório. source-pins-and-hashes.txt registra os commits e hashes usados nesta revalidação. A auditoria da tentativa Lean 4.35 segue separada e incompleta, em ../lean435-validation-incomplete/.
