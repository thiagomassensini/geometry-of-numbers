# Próximos passos da missão

**Estado conferido em 2026-11-07 contra `origin/main@24f61b01732f44599869350c4bf675c3f3a3dcb6`, após as PRs #240 e #241:** C0–C4 estão concluídos e integrados à `main`. C1B foi integrada pela PR #155 (merge `0586e238441096ecd2248e3f14bdac3a832af427`); C2 e C3 também estão integrados pelas PRs #157 e #159. Os módulos C2/C3 recompilaram em Lean 4.32 após o reinício; conferi que seus cinco módulos-fonte auditados não mudaram desde o snapshot compilado `b604c06dd0c13e7f77c65fb0634aa0b082d6c8d1`. A auditoria transitiva mais recente está em `evidence/c2-c3-current-main-20261107/`. As seções C2/C3 abaixo registram entregas concluídas, sem publicação pendente. A rota 4.32 publicada continua sendo a referência C2; o checkpoint 4.35 foi publicado pela PR #221 e continua preservado como validação incompleta. Retomar diretamente qualquer etapa posterior, sem repetir C0, C1, C1B, C2 ou C3.

## C2 — concluído e integrado

1. Trabalhar sobre a integração Lean 4.32 publicada em `b9ce1955c1e8830afad2323afe5266ed3f5f35d9`, usando-a como referência e não iniciando a migração geral 4.35.
2. A junção foi compilada: `SigmaRHHeightBridge.lean` reutiliza a única definição de `CarrySigmaObstruction.sigmaLineZero` de C1. Também foram removidas duas provas strip-local duplicadas da bridge.
3. O isolamento certificado, a decomposição exponencial completa do resto e o limite normalizado dos menores já foram compostos em
   `∃ P : ℕ, ∀ p ≥ P, sigmaPadeD (1/5) p < 0`.
4. Manter o resto analítico e as definições originais `completedSigmaLogJet` e `sigmaPadeD`. Não fechar o resultado adicionando hipóteses de sinal.
5. Integrado pela PR #157: commit de prova `bd1a6a04b8f98c33526059968c7fc079d48467f9`, merge na `main` `f4f5cf5ecc60ea3747cbaf21389fab52832d3949`. Build e auditorias locais passaram; o GitHub não retornou status checks. Evidências: `evidence/c2-eventual-negativity/`.

## C3 — concluído e integrado

6. Integrado pela PR #159, commit de prova `35dc14f13bd314639ce0c65daedf32b20f298667`, merge `b9cae2c0f4291ba7968c3ded2f2fecedf71cf9e8`.
7. As janelas `p=2i` e `p=2i+1` cobrem explicitamente os setores par e ímpar; C1B transporta cada direção negativa a todas as dimensões `M≥i+2`. Build e auditorias locais passaram; o GitHub não retornou status checks. Evidências: `evidence/c3-parity/`.

## Retomada do overlay 4.35

A tentativa está preservada como evidência incompleta em evidence/lean435-validation-incomplete/. Os antigos diretórios temporários desapareceram no reinício; o README agora registra como reconstruir a tentativa a partir do commit-base, reaplicar os patches e executar o scheduler. Retomar apenas se a rota 4.32 revelar um bloqueio concreto. A revalidação focada C2/C3 está em evidence/c2-c3-post-reboot-20261106/.

## C4 — concluído e integrado

Integrado pela PR #162, commit `31d3df33d4524d9809c75ba4481b1fa9f57a98bc`, merge `799a0e06af5469e9fe0665943adbb1cb29d0b6f8`. `SigmaSourceBezout.lean` prova a descida local do produto deslocado para `u=t²`, a recorrência formal `C_d · H_d=-C_d′` com `H_d(n)=2*completedSigmaLogJet d n`, e a congruência de Bézout com `2 • sigmaMatrix` original. A auditoria de axiomas passou; os logs, pins e hashes estão em `evidence/c4-source-bezout/`. Não houve status checks hospedados.

A lei quantitativa distância × profundidade e os novos cadernos continuam adiados. Não foi necessário calcular a primeira profundidade de falha para provar a negatividade eventual de C2. A rota 4.35 permanece somente como checkpoint incompleto; a rota 4.32 publicada continua sendo a referência validada para C2.
