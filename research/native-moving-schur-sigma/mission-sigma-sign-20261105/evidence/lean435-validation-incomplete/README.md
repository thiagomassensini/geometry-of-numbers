# Checkpoint de validação Lean 4.35 — incompleto

Este diretório preserva o estado da tentativa 4.35 até 2026-11-05. É um checkpoint de continuidade, não uma integração validada nem uma migração de Geometry/Carry. A rota principal para C2 volta a ser a integração publicada em Lean 4.32, no commit `b9ce1955c1e8830afad2323afe5266ed3f5f35d9`.

## O que foi preservado

- `integration-overrides/`: todos os overlays temporários aplicados à cadeia Geometry/Carry, incluindo o patch incompleto atual.
- `tracked-source-overrides/` e `tracked-source-overrides.patch.gz`: mudança local na fonte Geometry fora da pasta de overlays.
- `logs-lean435.tar.gz`: arquivo compactado byte a byte dos logs por módulo, status dos dois runs, falha mais recente do compilador, build externo e build completo Geometry.
- `compile-integration-435.py` e `integration-modules435.*`: scheduler e manifest da closure focada.
- `lean-toolchain`, `lakefile.toml`, `lake-manifest.json` e `geometry-pins-4.35.patch.gz`: pins usados na tentativa.
- `external-zeta-lab-pins/`: pins do desenvolvimento externo de certificado.
- `root-build.log` dentro do arquivo de logs: saída do build completo de Geometry que encontrou incompatibilidades fora da closure focada.

Os artefatos compilados `.olean` não são armazenados no Git. A cópia local de aceleração estava em `/tmp/geometry-of-numbers-native-sigma-4.35-rerun/research/native-moving-schur-sigma/.build435` (cerca de 79 MB) e pode ser reconstruída pelo scheduler.

## Pins e resultados que já passaram

- Geometry/Lean: `leanprover/lean4:v4.35.0-rc2`.
- Mathlib: `065356127b1dc0016f66b7283ce0ce2c4055aa55`.
- GreenFrame: `cd2d838bee67ad23f869a02f8ed9f0a0feb926fa`.
- O desenvolvimento externo é `teal-sea/zeta-lab@b09fa4dd2f2182cf14b248e7ffc64ff03df2c534`; seu build completo Lean 4.35 e checker de axiomas passaram. O log correspondente está dentro de `logs-lean435.tar.gz` em `logs/zeta-lab-lean435-full-build.log`.
- No último run do scheduler, 100 outputs prévios foram reutilizados e nove módulos novos compilaram antes da primeira falha. O primeiro run preservado registra mais 28 módulos concluídos antes de parar. Os status estão em `integration-build435/status.log` e `integration-build435/status-attempt1.log` dentro do arquivo.

## Último impedimento concreto observado

O primeiro módulo que interrompeu o último scheduler foi `CarrySelfAdjointOperator.RealLinearPMapReciprocalBlock`. A API 4.35 de `LinearPMap.inverse_apply_eq` espera `T.ker = ⊥`, enquanto o fonte-base fornece `LinearMap.ker T.toFun = ⊥`. Após começar a adaptar o overlay para `.ker`, a tentativa direta mais recente parou na declaração `realAdjoint_ker_eq_bot_of_denseRange`: a prova antiga via `LinearMap.ker_eq_bot'` deixa agora um objetivo de injetividade entre elementos do domínio subtype, e o uso de `Subtype.ext` na linha 44 não fecha esse objetivo. O diagnóstico integral está em `logs/direct-latest-error.log` dentro do arquivo; o erro do scheduler e os erros de tipos de domínio dos blocos fora da diagonal também foram preservados.

Esse é um bloqueio da portabilidade da closure inteira, não um impedimento já demonstrado à prova C2 em 4.32. Não continuar essa migração antes de verificar a rota 4.32. Os diagnósticos podem ser lidos extraindo `logs-lean435.tar.gz`.

## Comandos de retomada

No mesmo host, mantendo o checkout temporário atual:

```bash
cd /tmp/geometry-of-numbers-native-sigma-4.35-rerun
python3 compile-integration-435.py
```

O scheduler lê os patches de `integration-overrides/`, que permanecem no checkout temporário e também estão arquivados neste checkpoint. Para reaplicar os patches arquivados a uma reconstrução do checkout, copie `integration-overrides/` para a raiz do checkout 4.35 com esse mesmo nome, restaure os três arquivos de pins listados acima, e então execute o scheduler. Os manifests em `integration-modules435.*` registram a closure planejada.

Para reproduzir somente a última falha do overlay no mesmo host:

```bash
cd /tmp/geometry-of-numbers-native-sigma-4.35-rerun
GEOM=/tmp/geometry-of-numbers-native-sigma-4.35-rerun
OUT=$GEOM/research/native-moving-schur-sigma/.build435
LP="$OUT:$(cd "$GEOM" && lake env printenv LEAN_PATH | tr ':' '\n' | rg -v '/.lake/packages/GreenFrame/.lake/build/lib/lean' | paste -sd:)"
LEAN_PATH="$LP" /home/thlinux/.elan/toolchains/leanprover--lean4---v4.35.0-rc2/bin/lean \
  --root="$GEOM/integration-overrides/CarrySelfAdjointOperator" \
  -o "$OUT/CarrySelfAdjointOperator/RealLinearPMapReciprocalBlock.olean" \
  "$GEOM/integration-overrides/CarrySelfAdjointOperator/CarrySelfAdjointOperator/RealLinearPMapReciprocalBlock.lean"
```

Para C2, começar pelo código-fonte 4.32 no commit indicado no `SESSION_STATE.md`; não é necessário calcular a primeira profundidade de falha.
