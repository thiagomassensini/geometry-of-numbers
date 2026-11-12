# Checkpoint — C3 cofactor / third odd pivot

- MISSÃO: certificar o pivô canônico pela fonte C3 completada e transportar o sinal ao déficit quiral.
- BASE_SHA: `5f74e8ad1929f402562159d45ff8b72a13b573c9`, merge de #323.
- BRANCH: `agent/c3-cofactor-canonical-transport-20261112`.
- Últimos commits matemáticos: `3e1f6b7` (ímpar e quiral), `bde43be` (par e normalização).
- FASE: ambos os pivôs e transporte quiral validados, consolidação concluída.
- STATUS: GREEN para `s=0,1,n=2` e para o primeiro déficit quiral relativo ímpar na escala 11.
- ARQUIVOS NOVOS: `CofactorTransport.lean`, `NativeOddCertificate.lean`, `NativeEvenCertificate.lean`, `CertificateAudit.lean`, `compare_c3_heads.py`.
- TEOREMAS: margem cofactorial estrita, determinante Bézout, Schur da fonte, pivô Hankel, cofactor normalizado igual à direção física, coeficiente limite positivo e déficit eventualmente positivo. No setor par, determinante Bézout > `3/10^24` e pivô Hankel positivo.
- BUILD: `validate.sh` passou com avisos como erros. Auditoria de 17 resultados, 945 teoremas da missão e 66.019 dependências. Axiomas: `propext`, `Classical.choice`, `Quot.sound`.
- CHECKS: regressões racionais e C3/48–C3/256 passaram. `lake build --wfail` (8.850 tarefas), três auditorias raiz e `git diff --check` passaram.
- PRs integradas: #316–#317 (lei geral e registro), #318–#322 (cofator, C3/48 e limite condicional), #323 (caixas nativas e matriz ímpar).
- BLOQUEIO: nenhum na prova ou na validação local.
- INTEGRAÇÃO: PR desta branch para `main`. O GitHub registra o SHA em `mergeCommit`.
- PRÓXIMA AÇÃO MATEMÁTICA: a sensibilidade paramétrica das células C2 é opcional e pode ser estudada separadamente.
