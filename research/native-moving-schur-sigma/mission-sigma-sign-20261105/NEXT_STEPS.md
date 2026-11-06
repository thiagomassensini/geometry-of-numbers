# Próximos passos da missão

## C2 — concluído e integrado

1. Trabalhar sobre a integração Lean 4.32 publicada em `b9ce1955c1e8830afad2323afe5266ed3f5f35d9`, usando-a como referência e não iniciando a migração geral 4.35.
2. A junção foi compilada: `SigmaRHHeightBridge.lean` reutiliza a única definição de `CarrySigmaObstruction.sigmaLineZero` de C1. Também foram removidas duas provas strip-local duplicadas da bridge.
3. O isolamento certificado, a decomposição exponencial completa do resto e o limite normalizado dos menores já foram compostos em
   `∃ P : ℕ, ∀ p ≥ P, sigmaPadeD (1/5) p < 0`.
4. Manter o resto analítico e as definições originais `completedSigmaLogJet` e `sigmaPadeD`. Não fechar o resultado adicionando hipóteses de sinal.
5. Integrado pela PR #157: commit de prova `bd1a6a04b8f98c33526059968c7fc079d48467f9`, merge na `main` `f4f5cf5ecc60ea3747cbaf21389fab52832d3949`. Build e auditorias locais passaram; o GitHub não retornou status checks. Evidências: `evidence/c2-eventual-negativity/`.

## C3 — transporte aos setores par e ímpar

6. **Prova concluída:** `p = 2i` e `p = 2i + 1` dão as janelas `sigmaMatrix (1/5) 0 (i+2)` e `sigmaMatrix (1/5) 1 (i+2)`, respectivamente.
7. **Prova concluída:** o lema de persistência integrado em C1B (PR #155, merge `0586e238441096ecd2248e3f14bdac3a832af427`) leva cada direção a todas as dimensões `M ≥ i+2`. A auditoria e o checkpoint estão em `evidence/c3-parity/`; publicar a PR e integrar à `main`, depois atualizar este estado com os identificadores finais.

## Retomada do overlay 4.35

A tentativa está preservada como evidência incompleta em `evidence/lean435-validation-incomplete/`. Retomar apenas se a rota 4.32 revelar um bloqueio concreto. O ponto de parada, as declarações e os comandos estão registrados no README desse checkpoint.

Lei quantitativa distância × profundidade, novos cadernos e C4 ficam para depois de C2 e C3. Não é necessário calcular a primeira profundidade de falha para provar a negatividade eventual.
