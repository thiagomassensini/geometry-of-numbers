# Próximos passos da missão

**Estado conferido em 2026-11-07 contra `origin/main@71721874eb01071a07c83e4f71117b7d662e1b53`, após a PR #283:** C0–C4 estão concluídos e integrados à `main`. C1B foi integrada pela PR #155 (merge `0586e238441096ecd2248e3f14bdac3a832af427`); C2 e C3 também estão integrados pelas PRs #157 e #159. Os módulos C2/C3 recompilaram em Lean 4.32 após o reinício. A comparação dos módulos auditados entre a ponta documental anterior `24f61b01732f44599869350c4bf675c3f3a3dcb6` e esta revisão não encontrou mudanças; a compilação e a auditoria transitiva arquivadas (133 raízes e 70.861 dependências) continuam aplicáveis. C1B, C2 e C3 não têm prova nem publicação pendente. A rota 4.32 publicada continua sendo a referência C2; o checkpoint 4.35 da PR #221 permanece preservado e incompleto. Retomar diretamente qualquer etapa posterior, sem repetir C0, C1, C1B, C2 ou C3.

## C2 — concluído e integrado

1. A referência inicial foi a integração Lean 4.32 publicada em `b9ce1955c1e8830afad2323afe5266ed3f5f35d9`; não foi necessária migração geral para Lean 4.35.
2. A junção foi compilada: `SigmaRHHeightBridge.lean` reutiliza a única definição de `CarrySigmaObstruction.sigmaLineZero` de C1. Também foram removidas duas provas strip-local duplicadas da bridge.
3. O isolamento certificado, a decomposição exponencial completa do resto e o limite normalizado dos menores foram compostos em
   `∃ P : ℕ, ∀ p ≥ P, sigmaPadeD (1/5) p < 0`.
4. O resultado preserva o resto analítico e as definições originais `completedSigmaLogJet` e `sigmaPadeD`, sem adicionar hipóteses de sinal.
5. Integrado pela PR #157: commit de prova `bd1a6a04b8f98c33526059968c7fc079d48467f9`, merge na `main` `f4f5cf5ecc60ea3747cbaf21389fab52832d3949`. Build e auditorias locais passaram; o GitHub não retornou status checks. Evidências: `evidence/c2-eventual-negativity/`.

## C3 — concluído e integrado

6. Integrado pela PR #159, commit de prova `35dc14f13bd314639ce0c65daedf32b20f298667`, merge `b9cae2c0f4291ba7968c3ded2f2fecedf71cf9e8`.
7. As janelas `p=2i` e `p=2i+1` cobrem explicitamente os setores par e ímpar; C1B transporta cada direção negativa a todas as dimensões `M≥i+2`. Build e auditorias locais passaram; o GitHub não retornou status checks. Evidências: `evidence/c3-parity/`.

## Retomada do overlay 4.35

A tentativa está preservada como evidência incompleta em evidence/lean435-validation-incomplete/. Os antigos diretórios temporários desapareceram no reinício; o README agora registra como reconstruir a tentativa a partir do commit-base, reaplicar os patches e executar o scheduler. Retomar apenas se a rota 4.32 revelar um bloqueio concreto. A revalidação focada C2/C3 está em evidence/c2-c3-post-reboot-20261106/.

## C4 — concluído e integrado

Integrado pela PR #162, commit `31d3df33d4524d9809c75ba4481b1fa9f57a98bc`, merge `799a0e06af5469e9fe0665943adbb1cb29d0b6f8`. `SigmaSourceBezout.lean` prova a descida local do produto deslocado para `u=t²`, a recorrência formal `C_d · H_d=-C_d′` com `H_d(n)=2*completedSigmaLogJet d n`, e a congruência de Bézout com `2 • sigmaMatrix` original. A auditoria de axiomas passou; os logs, pins e hashes estão em `evidence/c4-source-bezout/`. Não houve status checks hospedados.

A lei quantitativa distância × profundidade e os novos cadernos continuam adiados. Não foi necessário calcular a primeira profundidade de falha para provar a negatividade eventual de C2. A rota 4.35 permanece somente como checkpoint incompleto; a rota 4.32 publicada continua sendo a referência validada para C2.
