# C5 — tentativas de arredondamento do estágio 3

As tentativas abaixo foram preservadas ao decompor a prova de `c5ZeroExpStage3_eq`.

- `SigmaC5ZeroExpStagesCertificate.first-attempt.failed.lean` e
  `first-stage3-build-interrupted.log`: tentativa direta que provava cada piso/teto
  expandindo toda a multiplicação intervalar. Foi interrompida após 10 minutos de
  CPU, sem erro Lean e com mais de 59 GiB disponíveis.
- `SigmaC5ZeroExpStagesCertificate.full-rebuild-interrupted.lean` e
  `full-rebuild-interrupted.log`: segunda tentativa, agora com fórmulas explícitas
  dos extremos, mas ainda no módulo que recompilava os estágios 0–2 já integrados.
  Foi interrompida para isolar o estágio 3 num módulo que importe a prova do
  estágio 2. Não houve erro Lean. A cópia de trabalho anterior à divisão está
  preservada em `../SigmaC5ZeroExpStagesCertificate.pre-split.lean`.
- `SigmaC5Stage3IntervalProbe.lean` e `interval-formula-probe-build.log`: sonda
  Lean 4.32 que confirmou por aritmética racional as quatro expressões exatas da
  caixa quadrada do estágio 2; `BUILD_EXIT=0`.

O resultado final está em `SigmaC5ZeroExpStage3Certificate.lean`, com build e
sobreposição de axiomas próprios registrados no checkpoint adjacente.
