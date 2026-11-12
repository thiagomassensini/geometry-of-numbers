# Checkpoint — C3 cofactor / third odd pivot

MISSÃO: certificar cofactorialmente o terceiro pivô ímpar pela fonte C3 completada e transportar ao saldo quiral.
BASE_SHA: `e4f5de51cad523963a327c8295067f88fc7855fa` (`origin/main` após PR #320 e #321).
BRANCH: `agent/c3-cofactor-chiral-certification-20261112-next`.
HEAD_SHA: `e4f5de51cad523963a327c8295067f88fc7855fa` (branch recém-criada; árvore limpa).
FASE: Checkpoint 0 concluído; Missão A ainda não satisfeita em dimensão geral.
STATUS: PARTIAL; nenhum certificado de sinal para o terceiro pivô foi alegado.
ÚLTIMO COMMIT: `e4f5de5` (main; PR #321, documentação de proveniência, integrada).
ARQUIVOS NOVOS: nenhum nesta continuação; reutilizar `CofactorIdentity.lean`, `SchurGate.lean`, `GammaHeadCrosswalk.lean` e os módulos C3 existentes.
TEOREMAS PROVADOS: identidade cofactorial 3×3 e vetor associado sem prefixo inversível; gate PosDef condicional; crosswalk Gamma/cauda até ordem 12. Falta a identidade abstrata para qualquer dimensão pedida na Missão A.
BUILD QUE PASSOU: branch base contém validação de 19 módulos com warnings como erros, `lake build --wfail` (8.850 jobs) e três auditorias; são evidências do commit integrado anterior.
CHECKS PENDENTES: compilar e auditar imediatamente o novo módulo geral; revisar a regressão abstrata e integrar seus imports no validador específico.
BLOQUEIO ATUAL: nenhum.
PRÓXIMA AÇÃO EXATA: provar, para `A : Matrix (Fin n)`, o determinante bordeado geral sem hipótese de invertibilidade, usando expansão de cofatores/Cramer, e deduzir as identidades do vetor cofactorial.

Registros prévios integrados: PR #318 merge `21c24415de48b184f5ad0498f9ac28e7c64a8195`; PR #319 `d4df30eb426653121c42cfe1bcfed68d3ce9bfed`; PR #320 `f5b403f31cc63a1f1a4af069180b0516f88841f1`; PR #321 `e4f5de51cad523963a327c8295067f88fc7855fa`.
Pins mantidos: Lean 4.32.0, mathlib `81a5d257`, GreenFrame `cd2d838`. A árvore original com alterações preexistentes segue preservada.
