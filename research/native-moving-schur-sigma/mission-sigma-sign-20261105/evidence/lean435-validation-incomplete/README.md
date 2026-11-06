# Checkpoint de validação Lean 4.35 — incompleto

Este diretório preserva a tentativa 4.35 executada em 2026-11-05; os comandos de reconstrução foram atualizados em 2026-11-06 após o reboot. É um checkpoint de continuidade, não uma integração validada nem uma migração de Geometry/Carry. A rota principal para C2 é a integração publicada em Lean 4.32, no commit `b9ce1955c1e8830afad2323afe5266ed3f5f35d9`; C2/C3 estão concluídos nessa rota.

## O que foi preservado

- `integration-overrides/`: todos os overlays temporários aplicados à cadeia Geometry/Carry, incluindo o patch incompleto atual.
- `tracked-source-overrides/` e `tracked-source-overrides.patch.gz`: mudança local na fonte Geometry fora da pasta de overlays.
- `logs-lean435.tar.gz`: arquivo compactado byte a byte dos logs por módulo, status dos dois runs, falha mais recente do compilador, build externo e build completo Geometry.
- `compile-integration-435.py` e `integration-modules435.*`: scheduler e manifest da closure focada.
- `lean-toolchain`, `lakefile.toml`, `lake-manifest.json` e `geometry-pins-4.35.patch.gz`: pins usados na tentativa.
- `external-zeta-lab-pins/`: pins do desenvolvimento externo de certificado.
- `root-build.log` dentro do arquivo de logs: saída do build completo de Geometry que encontrou incompatibilidades fora da closure focada.

Os artefatos compilados `.olean` não são armazenados no Git. As worktrees temporárias originais em `/tmp` desapareceram no reinício do servidor; seus patches, pins, manifests, logs e erros continuam versionados aqui. A cópia `.olean` não é necessária para recuperar o estado e pode ser reconstruída pelo scheduler.

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

O checkout temporário original não existe mais. Para reconstruir a tentativa exatamente sobre sua base Lean 4.32, reaplique os arquivos duráveis da `main` ao commit `353a7db22ca3b886ff111d0e61827784a4eb6053`:

```bash
GEOM=/home/thlinux/worktrees/geometry-of-numbers-native-sigma-4.35-resume
git clone https://github.com/thiagomassensini/geometry-of-numbers.git "$GEOM"
git -C "$GEOM" checkout --detach 353a7db22ca3b886ff111d0e61827784a4eb6053
git -C "$GEOM" fetch origin main
git -C "$GEOM" checkout origin/main -- research/native-moving-schur-sigma/mission-sigma-sign-20261105/evidence/lean435-validation-incomplete
EVIDENCE="$GEOM/research/native-moving-schur-sigma/mission-sigma-sign-20261105/evidence/lean435-validation-incomplete"
cp -a "$EVIDENCE/integration-overrides" "$GEOM/"
cp "$EVIDENCE/compile-integration-435.py" "$GEOM/"
cp "$EVIDENCE"/integration-modules435.* "$GEOM/"
gzip -dc "$EVIDENCE/geometry-pins-4.35.patch.gz" | git -C "$GEOM" apply
gzip -dc "$EVIDENCE/tracked-source-overrides.patch.gz" | git -C "$GEOM" apply
cp "$EVIDENCE/lean-toolchain" "$GEOM/lean-toolchain"
cp "$EVIDENCE/lakefile.toml" "$GEOM/lakefile.toml"
cp "$EVIDENCE/lake-manifest.json" "$GEOM/lake-manifest.json"
```

Depois de disponibilizar as dependências nos pins arquivados, execute o scheduler. Ele aceita caminhos explícitos para que a retomada não dependa do caminho temporário antigo:

```bash
SIGMA_435_GEOM_ROOT="$GEOM" \
SIGMA_435_CARRY_ROOT=/home/thlinux/carry-self-adjoint-operator \
SIGMA_435_OUTPUT_DIR="$GEOM/research/native-moving-schur-sigma/.build435" \
SIGMA_435_LOG_DIR="$GEOM/integration-build435" \
LEAN_BIN=/home/thlinux/.elan/toolchains/leanprover--lean4---v4.35.0-rc2/bin/lean \
python3 "$GEOM/compile-integration-435.py"
```

Para reproduzir somente o último erro direto, depois de reconstruir os outputs necessários:

```bash
OUT="$GEOM/research/native-moving-schur-sigma/.build435"
LP="$OUT:$(cd "$GEOM" && lake env printenv LEAN_PATH | tr ':' '\n' | rg -v '/.lake/packages/GreenFrame/.lake/build/lib/lean' | paste -sd:)"
LEAN_PATH="$LP" /home/thlinux/.elan/toolchains/leanprover--lean4---v4.35.0-rc2/bin/lean \
  --root="$GEOM/integration-overrides/CarrySelfAdjointOperator" \
  -o "$OUT/CarrySelfAdjointOperator/RealLinearPMapReciprocalBlock.olean" \
  "$GEOM/integration-overrides/CarrySelfAdjointOperator/CarrySelfAdjointOperator/RealLinearPMapReciprocalBlock.lean"
```

O scheduler e os overlays são apenas para continuidade da tentativa incompleta 4.35. Para C2/C3, usar a prova e a validação 4.32 já integradas. Não calcular a primeira profundidade de falha para provar a negatividade eventual.
