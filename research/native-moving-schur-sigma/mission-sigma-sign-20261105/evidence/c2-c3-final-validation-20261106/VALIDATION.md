# Revalidação final de C2/C3 na main atual

**Base das fontes:** `9951fcb7315c25b6d878befc42b2d02c26a96ec7` (PR #203, cuja alteração foi documental).
**Toolchain:** Lean 4.32.0, `-DwarningAsError=true`.
**Escopo:** recompilação dos módulos finais C2/C3 das fontes dessa revisão e auditoria transitiva. Os módulos-base compartilhados foram reutilizados do cache de validação 4.32 em `67aea3263426cc8f9787f34aa7833a5650dde175`; as fontes C2/C3 foram compiladas novamente a partir da revisão `9951fcb`.

## Resultados

- `SigmaPadeEventualNegativity.lean` compilou. O checker aceitou `exists_eventually_negative_sigmaPadeD_from_height50_certificate` com apenas `propext`, `Classical.choice` e `Quot.sound`.
- `SigmaParityNegativeDirection.lean` compilou. O checker aceitou os quatro roots C3, também com apenas esses axiomas padrão.
- `SigmaPadeAudit.lean` compilou e percorreu 133 roots públicos e 70.861 dependências de tipo/corpo. Nenhum axioma fora dos três padrão foi encontrado; a auditoria confirmou a dependência da característica original e de `completedSigmaLogJet`.
- A definição de `CarrySigmaObstruction.sigmaLineZero` aparece uma vez, em `SigmaCertifiedNegativeDirection.lean`; a bridge C2 a reutiliza.

## Conteúdo matemático confirmado

C2 continua provando, nos momentos originais,

```text
∃ P : ℕ, ∀ p ≥ P, sigmaPadeD (1/5) p < 0.
```

A composição usa `exists_firstSigmaDisplacedProductIsolation_from_height50_certificate`, `completedNative_sigmaRemainder_square_decomposition_of_isolation`, `sigmaPadeNormalizedMinors_tendsto_of_unitCircle_twoPole_remainder` e `sigmaPadeD_eventually_neg_of_normalized_limit`. Ela preserva `completedSigmaLogJet` e `sigmaPadeD`, mantendo o resto exponencial na convergência dos menores normalizados. Não há hipótese adicional de sinal. A referência de integração é a rota publicada em Lean 4.32, iniciada no commit `b9ce1955c1e8830afad2323afe5266ed3f5f35d9` com `SigmaHeight50Integration.lean`; a tentativa geral 4.35 continua apenas como checkpoint incompleto.

C3 usa explicitamente `p=2P` para o setor par `sigmaMatrix (1/5) 0` e `p=2P+1` para o setor ímpar `sigmaMatrix (1/5) 1`. Em cada setor, a direção negativa da janela é transportada às dimensões `M ≥ P+2`.

## Reprodução

Os scripts `compile_sigma_pade.sh`, `check_c2_axioms.py` e `check_c3_axioms.py` estão versionados junto com os módulos. A compilação usou o checkout Carry limpo no pin `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`, e os logs e hashes estão neste diretório. A tentativa Lean 4.35 preserva separadamente seus patches, pins, erro e comandos de retomada em `../lean435-validation-incomplete/`.

C2 e C3 já estavam integrados pelas PRs #157 e #159. Este checkpoint registra a revalidação das fontes atuais; não altera as provas.
