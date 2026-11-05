# Relatório consolidado — missão de negatividade transversal sigma

**Atualizado em 2026-11-05.** C0 foi integrado pela PR #153. C1 está formalmente concluído e passou a compilação focada e a auditoria de axiomas; commit e PR da entrega C1 ainda estão pendentes nesta atualização.

## Resultado matemático concluído

Foi compilado o teorema:

```lean
CarrySigmaObstruction.certified_sigma_negative_direction_of_nonzero_small_shift
    (d : ℝ) (hd₀ : 0 < |d|) (hd₁ : |d| < (1 / 4 : ℝ)) :
    ∃ N : ℕ, ∃ v : Fin N → ℝ, v ≠ 0 ∧
      v ⬝ᵥ (sigmaMatrix d 0 N *ᵥ v) < 0
```

A prova reutiliza o certificado formal `HardyFirstZero.first_zero_on_line`, converte o zero da zeta em zero da continuação nativa pela equivalência no strip, volta à característica nativa original usando `completedNativeCharacteristicContinuation_eq_native` somente dentro do domínio demonstrado e aplica `exists_sigmaMatrix_negative_direction_of_zero`. A conclusão é sobre os jets e a matriz `sigmaMatrix` originais.

O corolário final e o certificado de primeiro zero dependem apenas de `propext`, `Classical.choice` e `Quot.sound`. A auditoria automática aceitou 106 relatórios; a varredura dos fontes C1 não achou `sorry`, `admit`, `native_decide`, `sorryAx` nem axiomas novos.

## Estado dos checkpoints

| Checkpoint | Estado | Resultado/evidência |
|---|---|---|
| C0 — recuperação e inventário | Integrado | PR #153; merge commit `2a3e89987beeb05d29b2e71d8b8ed6851383ccaa` |
| C1 — direção negativa finita para todo `0<|d|<1/4` | Prova concluída e validada localmente | Teorema acima; logs de build e axiom checker em `evidence/` |
| C1B — persistência em dimensões maiores | Aberto | Falta bloco prefixo principal e prolongamento por zeros |
| C2 — menores originais eventualmente negativos em `d=1/5` | Aberto | Requer composição Padé e isolamento certificado |
| C3 — torres par e ímpar | Aberto | Depende de C2 e C1B |
| C4 — fonte deslocada e Bézout | Não iniciado | Explorar por último, com o fator 2 explícito |

## Compilação, auditoria e pins

- O build completo da raiz em Lean 4.32, iniciado no checkout sem cache, terminou em 8.857/8.857 jobs. `evidence/c1-root-build.log` guarda a execução capturada depois que o cache ficou aquecido (8.850 jobs).
- O comando focado `SIGMA_OUTPUT_DIR=/tmp/sigma-c1-certified-20261105 research/native-moving-schur-sigma/compile_c1.sh` recompilou os fontes locais relevantes, os módulos sigma portados, a ponte mínima e os dez módulos Lean do certificado do primeiro zero. `evidence/c1-focused-build.log` contém a saída final.
- O checker recursivo confirmou que 1.278 módulos-fonte não-Mathlib no fechamento importado correspondem aos commits/pins registrados. A lista e o resultado estão em `evidence/c1-source-pin-audit.txt`.
- Os caches de `.olean` externos de Lean/Mathlib/Carry foram usados a partir de checkouts com versões explícitas; o build focado não é uma recompilação limpa de toda essa árvore externa. A prova C1 e seu fechamento local foram compilados fresh na pasta de saída temporária.
- Fontes copiadas, licenças, pins e hashes estão descritos em `evidence/c1-source-provenance.md` e `evidence/c1-source-sha256.txt`.
- C1 foi preparado em uma branch nova sobre a `main` que já contém C0. A PR C1 e o status hospedado ainda precisam ser verificados após publicação.

## Limites e próxima lacuna

C1 prova que para cada deslocamento admissível existe alguma dimensão finita com uma direção negativa. Ainda não prova que a mesma negatividade persiste em toda dimensão maior; isso é C1B. Tampouco afirma negatividade de todos os pivôs, crescimento do índice negativo, positividade central all-order ou RH. C2 ainda precisa demonstrar negatividade eventual dos menores dos jets originais, e C3 precisa transportá-la às duas torres.
