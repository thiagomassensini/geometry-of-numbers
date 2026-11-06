# Replay das caixas intervalares — 2026-11-06

## Resultado

O checkout Momentos está em `68c9b5f0a196289e28a8e5586146707d27df6b75`
(`origin/research/sigma-pade-dimension-depth-20261104`) e permaneceu sem
alterações. A geração foi feita numa cópia temporária da pasta de investigação
em `/tmp/c5-gamma-repro-20261106`, com a correção local preservada em
`momentos-gmpy2-compat.patch`. O patch apenas converte os mantissas e os
numeradores/denominadores `gmpy2.mpz` em `int` nativo antes da construção de
`Fraction`/`Decimal`; não altera a fórmula do avaliador.

As três execuções da retomada sem aplicar o patch pararam ao converter
`gmpy2.mpz` para `Decimal`, antes de escrever JSON. A falha original, com
traceback, está em `sign1024_stirling-initial-gmpy2-failure.log`. Depois de
aplicar o patch somente à cópia temporária, todas as gerações terminaram com
`REPRO_EXIT=0`; o verificador independente usou apenas frações racionais e
também passou:

| `d` | Corte | Nós | Raios `r/R` | Sinais | Evidência |
|---|---:|---:|---:|---|---|
| `0.0495` | 0 | 1024 | `0.3/0.4` | `+++++++++++-` | `sign1024_stirling-reproduced.*` |
| `0.0495` | 12 | 512 | `0.2/0.4` | `+++++++++++-` | `sign512_stirling_L12-reproduced.*` |
| `0.1` | 12 | 512 | `0.15/0.3` | `+++++++++-` | `sign512_d01_L12-reproduced.*` |

Nos três casos, deslocamento, sinais, caixas decimais racionais dos
coeficientes, positividade de `c₀` e intervalos dos menores coincidem com os
JSONs arquivados antes deste replay.

Ambiente observado: Python `3.12.12`, mpmath `1.3.0`, gmpy2 `2.2.1`. O cálculo
experimental usa `mpmath.iv`; isto **não** prova que os coeficientes verdadeiros
da fonte C2 original pertençam às caixas. A checagem exata confirma somente os
sinais racionais condicionais às caixas. A inclusão formal em Lean continua
aberta em O4/C5.

## Comandos reproduzidos

O diretório de pesquisa fonte foi o checkout Momentos indicado acima. A partir
de `/home/thlinux`, a cópia e o patch foram preparados com:

```bash
mkdir -p /tmp/c5-gamma-repro-20261106/investigations
cp -a /home/thlinux/worktrees/momentos-c5-research/investigations/c2_first_negative_interval_certificate_20261106 \
  /tmp/c5-gamma-repro-20261106/investigations/
patch -d /tmp/c5-gamma-repro-20261106 -p1 < \
  /home/thlinux/worktrees/geometry-of-numbers-c5-weight-degree-2-14-20261106/research/native-moving-schur-sigma/mission-c5-finite-c2-certification/evidence/interval-certificate/momentos-gmpy2-compat.patch
```

Da raiz da cópia temporária, as gerações foram:

```bash
python3 investigations/c2_first_negative_interval_certificate_20261106/certify_finite_c2.py \
  --d 0.0495 --cutoff 0 --nodes 1024 --radius 0.3 --outer 0.4 --max-s 11 \
  --out /home/thlinux/worktrees/geometry-of-numbers-c5-weight-degree-2-14-20261106/research/native-moving-schur-sigma/mission-c5-finite-c2-certification/evidence/interval-certificate/sign1024_stirling-reproduced.json
python3 investigations/c2_first_negative_interval_certificate_20261106/certify_finite_c2.py \
  --d 0.0495 --cutoff 12 --nodes 512 --radius 0.2 --outer 0.4 --max-s 11 \
  --out /home/thlinux/worktrees/geometry-of-numbers-c5-weight-degree-2-14-20261106/research/native-moving-schur-sigma/mission-c5-finite-c2-certification/evidence/interval-certificate/sign512_stirling_L12-reproduced.json
python3 investigations/c2_first_negative_interval_certificate_20261106/certify_finite_c2.py \
  --d 0.1 --cutoff 12 --nodes 512 --radius 0.15 --outer 0.3 --max-s 9 \
  --out /home/thlinux/worktrees/geometry-of-numbers-c5-weight-degree-2-14-20261106/research/native-moving-schur-sigma/mission-c5-finite-c2-certification/evidence/interval-certificate/sign512_d01_L12-reproduced.json
```

Com o script `verify_signs_exact.py` da mesma revisão Momentos, cada JSON foi
verificado e a saída exata foi salva como `*.exact-checked.json`; os logs
`*.exact-check.log` contêm os limites racionais decimais dirigidos e as strings
de sinal.

## Arquivos desta evidência

- Patch e falha inicial: `momentos-gmpy2-compat.patch` e
  `sign1024_stirling-initial-gmpy2-failure.log`.
- Geração: três arquivos `*-reproduced.log` e três arquivos
  `*-reproduced.json`.
- Verificação independente: três arquivos `*.exact-check.log` e três arquivos
  `*.exact-checked.json`.
- Checksums desses arquivos e dos scripts fonte: `reproduction-2026-11-06-sha256.txt`.
