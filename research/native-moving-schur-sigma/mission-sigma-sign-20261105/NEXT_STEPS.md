# Próximos passos da missão

## C2 — negatividade eventual dos menores originais

1. Trabalhar sobre a integração Lean 4.32 publicada em `b9ce1955c1e8830afad2323afe5266ed3f5f35d9`, usando-a como referência e não iniciando a migração geral 4.35.
2. A junção foi compilada: `SigmaRHHeightBridge.lean` reutiliza a única definição de `CarrySigmaObstruction.sigmaLineZero` de C1. Também foram removidas duas provas strip-local duplicadas da bridge.
3. O isolamento certificado, a decomposição exponencial completa do resto e o limite normalizado dos menores já foram compostos em
   `∃ P : ℕ, ∀ p ≥ P, sigmaPadeD (1/5) p < 0`.
4. Manter o resto analítico e as definições originais `completedSigmaLogJet` e `sigmaPadeD`. Não fechar o resultado adicionando hipóteses de sinal.
5. A compilação Lean 4.32 e as auditorias externa, de integração e transitiva passaram. Publicar agora o checkpoint C2 em uma PR pequena, aguardar os gates, integrar à `main` e atualizar o estado com o merge.

## C3 — transporte aos setores par e ímpar

6. Só depois do merge de C2, usar `p = 2i` e `p = 2i + 1` para provar a cobertura explícita dos setores par e ímpar.
7. Transportar as direções negativas às dimensões maiores pelo teorema de persistência integrado em C1B (PR #155, merge `0586e238441096ecd2248e3f14bdac3a832af427`). Compilar, auditar axiomas, registrar checkpoint, publicar PR e integrar à `main`.

## Retomada do overlay 4.35

A tentativa está preservada como evidência incompleta em `evidence/lean435-validation-incomplete/`. Retomar apenas se a rota 4.32 revelar um bloqueio concreto. O ponto de parada, as declarações e os comandos estão registrados no README desse checkpoint.

Lei quantitativa distância × profundidade, novos cadernos e C4 ficam para depois de C2 e C3. Não é necessário calcular a primeira profundidade de falha para provar a negatividade eventual.
