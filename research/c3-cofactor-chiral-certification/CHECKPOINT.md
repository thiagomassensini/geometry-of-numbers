# Checkpoint — C3 cofactor / third odd pivot

- MISSÃO: certificar o pivô canônico pela fonte C3 completada e transportar o sinal ao déficit quiral.
- BASE_SHA: `5f74e8ad1929f402562159d45ff8b72a13b573c9`, merge de #323.
- BRANCH: `agent/c3-cofactor-canonical-transport-20261112`.
- Último commit anterior: `3e1f6b7` (pivô ímpar e limite quiral).
- FASE: ambos os pivôs e transporte quiral compilados.
- STATUS: GREEN para `s=0,1,n=2` e para o primeiro déficit quiral relativo ímpar na escala 11.
- ARQUIVOS NOVOS: `CofactorTransport.lean`, `NativeOddCertificate.lean`, `NativeEvenCertificate.lean`.
- TEOREMAS: margem cofactorial estrita, determinante Bézout, Schur da fonte, pivô Hankel, cofactor normalizado igual à direção física, coeficiente limite positivo e déficit eventualmente positivo. No setor par, determinante Bézout > `3/10^24` e pivô Hankel positivo.
- BUILD: três módulos novos compilados com Lean 4.32.0 e warnings como erros. Axiomas públicos: `propext`, `Classical.choice`, `Quot.sound`.
- PRs integradas: #316–#317 (lei geral e registro), #318–#322 (cofator, C3/48 e limite condicional), #323 (caixas nativas e matriz ímpar).
- PENDENTE: terminar a auditoria transitiva integrada, validador, relatório e PR.
- PRÓXIMA AÇÃO: acompanhar a execução do validador unificado e registrar o resultado.
