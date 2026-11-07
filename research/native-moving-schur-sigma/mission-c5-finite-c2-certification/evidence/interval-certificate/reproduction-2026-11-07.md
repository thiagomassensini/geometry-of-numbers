# Replay das caixas intervalares — 2026-11-07

## Resultado e limite

As três gerações foram repetidas a partir da revisão Momentos
`68c9b5f0a196289e28a8e5586146707d27df6b75`, em uma cópia temporária dos
scripts com o patch `momentos-gmpy2-compat.patch`. Todas terminaram com código
zero. O verificador independente, que opera apenas com frações racionais,
passou nos três JSONs:

| `d` | Corte | Nós | Raios `r/R` | Sinais exatos condicionais |
|---|---:|---:|---:|---|
| `0.0495` | 0 | 1024 | `0.3/0.4` | `+++++++++++-` |
| `0.0495` | 12 | 512 | `0.2/0.4` | `+++++++++++-` |
| `0.1` | 12 | 512 | `0.15/0.3` | `+++++++++-` |

Deslocamento, sinais, intervalos racionais dos coeficientes, positividade de
`c₀` e intervalos de `D_s` coincidem com os JSONs já arquivados no replay de
2026-11-06. Essa comparação foi feita campo a campo para cada saída. Os novos
JSONs, logs da geração, saídas do verificador exato e log da tentativa sem
patch estão preservados nesta pasta com o sufixo `rerun-2026-11-07`.

Isto continua sendo **validação numérica incompleta**, não prova Lean da
inclusão dos coeficientes verdadeiros nas caixas. A geração depende de
`mpmath.iv`; o verificador de frações prova somente os sinais condicionais às
caixas fornecidas. As obrigações C5/O4 não foram fechadas por este replay.

## Falha sem o patch

A primeira repetição foi executada sem modificar o checkout Momentos, que
estava limpo e destacado no commit acima. Após avaliar 256 amostras, o script
`certify_finite_c2.py` parou em `rounded`, linha 105, ao construir
`Decimal(fr.numerator)`:

```text
TypeError: conversion from gmpy2.mpz to Decimal is not supported
```

O traceback integral está em
`sign1024_stirling-rerun-initial-gmpy2-failure-2026-11-07.log`. Nenhum JSON foi
gerado nessa tentativa. O erro decorre do tipo inteiro fornecido pela versão
instalada de mpmath/gmpy2; não é uma falha no sinal racional.

## Patch e ambiente

O patch já arquivado altera somente conversões de mantissa, numerador e
denominador para `int` nativo antes de construir `Fraction`/`Decimal`. Não muda
fórmulas, parâmetros, tolerâncias nem caixas. A fonte Momentos permaneceu
intacta.

- Momentos: commit `68c9b5f0a196289e28a8e5586146707d27df6b75`, checkout limpo.
- Python `3.12.12`, mpmath `1.3.0`, gmpy2 `2.2.1`, SymPy `1.14.0`.
- SHA-256 dos scripts fonte e do patch: `reproduction-2026-11-07-sha256.txt`.
- SHA-256 dos novos JSONs e logs: `reproduction-2026-11-07-artifacts-sha256.txt`.

## Comandos de reprodução

Da raiz `/home/thlinux`, usando o checkout Momentos pinado e esta pasta de
evidências como `EVID`:

```bash
MOMENTS=/home/thlinux/worktrees/momentos-c5-research
EVID=/home/thlinux/worktrees/geometry-of-numbers-c5-phase0-replay-20261107/research/native-moving-schur-sigma/mission-c5-finite-c2-certification/evidence/interval-certificate
REPRO=/tmp/c5-phase0-rerun-20261107-02
mkdir -p "$REPRO/investigations"
cp -a "$MOMENTS/investigations/c2_first_negative_interval_certificate_20261106" "$REPRO/investigations/"
patch --batch -p1 -d "$REPRO" < "$EVID/momentos-gmpy2-compat.patch"
cd "$REPRO"
python3 investigations/c2_first_negative_interval_certificate_20261106/certify_finite_c2.py --d 0.0495 --cutoff 0 --nodes 1024 --radius 0.3 --outer 0.4 --max-s 11 --out "$EVID/sign1024_stirling-rerun-2026-11-07.json" > "$EVID/sign1024_stirling-rerun-2026-11-07.log" 2>&1
python3 investigations/c2_first_negative_interval_certificate_20261106/certify_finite_c2.py --d 0.0495 --cutoff 12 --nodes 512 --radius 0.2 --outer 0.4 --max-s 11 --out "$EVID/sign512_stirling_L12-rerun-2026-11-07.json" > "$EVID/sign512_stirling_L12-rerun-2026-11-07.log" 2>&1
python3 investigations/c2_first_negative_interval_certificate_20261106/certify_finite_c2.py --d 0.1 --cutoff 12 --nodes 512 --radius 0.15 --outer 0.3 --max-s 9 --out "$EVID/sign512_d01_L12-rerun-2026-11-07.json" > "$EVID/sign512_d01_L12-rerun-2026-11-07.log" 2>&1
python3 investigations/c2_first_negative_interval_certificate_20261106/verify_signs_exact.py "$EVID/sign1024_stirling-rerun-2026-11-07.json" "$EVID/sign1024_stirling-rerun-2026-11-07.exact-checked.json" > "$EVID/sign1024_stirling-rerun-2026-11-07.exact-check.log"
python3 investigations/c2_first_negative_interval_certificate_20261106/verify_signs_exact.py "$EVID/sign512_stirling_L12-rerun-2026-11-07.json" "$EVID/sign512_stirling_L12-rerun-2026-11-07.exact-checked.json" > "$EVID/sign512_stirling_L12-rerun-2026-11-07.exact-check.log"
python3 investigations/c2_first_negative_interval_certificate_20261106/verify_signs_exact.py "$EVID/sign512_d01_L12-rerun-2026-11-07.json" "$EVID/sign512_d01_L12-rerun-2026-11-07.exact-checked.json" > "$EVID/sign512_d01_L12-rerun-2026-11-07.exact-check.log"
```

A última linha de cada saída deve ser
`EXACT RATIONAL CHECK PASSED, contingent on coefficient inclusions.` e as
strings devem coincidir com a tabela acima. Para comparar com a geração
anterior, os arquivos sem sufixo de data permanecem preservados ao lado dos
novos.

## Próximo passo da missão

O próximo passo formal segue sendo provar a recorrência exata da caixa da
exponencial arredondada para `2 ≤ k ≤ 192`. Depois vêm a ponte CSV–Lean, a
composição da fonte C2 original e as inclusões O3. Este replay não altera essa
ordem nem fecha nenhum desses itens.
