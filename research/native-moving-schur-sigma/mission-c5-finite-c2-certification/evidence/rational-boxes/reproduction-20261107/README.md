# Reprodução dos sinais finitos C2 — 2026-11-07

**Status:** reprodução do avaliador intervalar e do verificador racional, ainda condicional às caixas experimentais. Isso não prova a inclusão dos coeficientes originais em Lean e não fecha C5.

## Saídas

As três configurações pedidas foram reproduzidas a partir do checkout Momentos na revisão `68c9b5f0a196289e28a8e5586146707d27df6b75`:

| Distância e corte | Nós; raios | Resultado do verificador racional |
|---|---|---|
| `d=0.0495`, `L=0` | `1024`; `r/R=0.3/0.4` | `+++++++++++-` |
| `d=0.0495`, `L=12` | `512`; `r/R=0.2/0.4` | `+++++++++++-` |
| `d=0.1`, `L=12` | `512`; `r/R=0.15/0.3` | `+++++++++-` |

Cada verificação dos sinais usa frações exatas. Os arquivos `sign*.json` guardam as caixas racionais produzidas; `sign*-verify.log` registra os limites dirigidos para fora de cada menor.

A primeira execução sem patch reproduziu a incompatibilidade local `gmpy2.mpz` → `Decimal`. A reprodução concluída aplicou o patch de compatibilidade já arquivado em `evidence/interval-certificate/momentos-gmpy2-compat.patch` somente no checkout isolado do Momentos. O checkout foi restaurado limpo depois; nenhuma branch publicada do Momentos foi alterada.

## Reproduzir

No checkout isolado do Momentos, com `mpmath`, `gmpy2` e `sympy` instalados, aplique o patch arquivado e execute os três comandos abaixo, usando caminhos de saída próprios:

```bash
git apply /path/to/geometry-of-numbers/research/native-moving-schur-sigma/mission-c5-finite-c2-certification/evidence/interval-certificate/momentos-gmpy2-compat.patch
python3 investigations/c2_first_negative_interval_certificate_20261106/certify_finite_c2.py --d 0.0495 --cutoff 0 --nodes 1024 --radius 0.3 --outer 0.4 --max-s 11 --out sign1024.json
python3 investigations/c2_first_negative_interval_certificate_20261106/verify_signs_exact.py sign1024.json
python3 investigations/c2_first_negative_interval_certificate_20261106/certify_finite_c2.py --d 0.0495 --cutoff 12 --nodes 512 --radius 0.2 --outer 0.4 --max-s 11 --out sign512-L12.json
python3 investigations/c2_first_negative_interval_certificate_20261106/verify_signs_exact.py sign512-L12.json
python3 investigations/c2_first_negative_interval_certificate_20261106/certify_finite_c2.py --d 0.1 --cutoff 12 --nodes 512 --radius 0.15 --outer 0.3 --max-s 9 --out sign512-d01-L12.json
python3 investigations/c2_first_negative_interval_certificate_20261106/verify_signs_exact.py sign512-d01-L12.json
git restore -- investigations/c2_first_negative_interval_certificate_20261106/certify_finite_c2.py
```

O primeiro erro sem patch está preservado em `sign1024-unpatched-failure.log`; as três execuções corrigidas e verificações estão nos logs correspondentes. Os JSONs e logs desta pasta estão listados em `SHA256SUMS.txt`.

## Limite lógico

Esta reprodução confirma novamente os sinais **dadas as caixas geradas**. O gerador ainda usa operações intervalares externas; esta etapa não certifica formalmente em Lean que os coeficientes `c₀…c₁₄` e `c₀…c₁₂` da fonte C2 original pertencem às caixas. As conclusões Lean O3 continuam condicionais a `sigmaC00495SourceBoxes` e `sigmaC01SourceBoxes`. C5 segue aberta.
