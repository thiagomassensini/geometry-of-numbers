# Checkpoint — C3 cofactor / third odd pivot

- MISSÃO: certificar o pivô canônico pela fonte C3 completada e transportar o sinal ao déficit quiral.
- BASE_SHA: `5f74e8ad1929f402562159d45ff8b72a13b573c9`, merge de #323.
- BRANCH: `agent/c3-cofactor-canonical-transport-20261112`.
- HEAD_SHA anterior: base acima. Este checkpoint acompanha o commit de transporte.
- FASE: pivô ímpar e transporte quiral compilados.
- STATUS: GREEN para `s=1,n=2` e para o primeiro déficit quiral relativo na escala 11.
- ARQUIVOS NOVOS: `CofactorTransport.lean`, `NativeOddCertificate.lean`.
- TEOREMAS: margem cofactorial estrita, determinante Bézout, Schur da fonte, pivô Hankel, cofactor normalizado igual à direção física, coeficiente limite positivo e déficit eventualmente positivo.
- BUILD: dois módulos novos compilados com Lean 4.32.0 e warnings como erros. Axiomas públicos: `propext`, `Classical.choice`, `Quot.sound`.
- PRs integradas: #316–#317 (lei geral e registro), #318–#322 (cofator, C3/48 e limite condicional), #323 (caixas nativas e matriz ímpar).
- PENDENTE: prova par, auditoria transitiva, validador unificado, relatório e PR.
- PRÓXIMA AÇÃO: verificar a margem par `3/10^24` em Lean usando as mesmas caixas.
