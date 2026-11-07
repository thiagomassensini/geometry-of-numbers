# C5 — recorrência Taylor do termo `m=2`, transição `n=18→19` (validação parcial)

## Resultado

`SigmaC5M2TaylorStateStage19Certificate.lean` prova
`c5RoundedExpStateC_stage19_correct` para o nó `(a,j)=(2/5,0)`, partindo do
estado `n=18` já integrado pela PR #275. O passo verifica a multiplicação da
potência por `c5M2TaylorArgExport`, o coeficiente exato
`1/18! = 1/6402373705728000`, o arredondamento em 896 bits e a soma acumulada.

O probe exporta seis extremos racionais exatos em
`state-stage19-export-probe.log`. No resultado de `n=19`, a potência tem sinal
negativo, o termo de Taylor tem sinal positivo e a soma acumulada continua
positiva. A prova cobre apenas essa transição em um único nó; não certifica os
outros nós, os demais termos, as quadraturas, a caixa C2 completa, as inclusões
da fonte nem os dois sinais finais. C5 permanece incompleta.

## Compilação e auditoria

Lean 4.32.0, com `warningAsError=true`, compilou o probe e o certificado. O
certificado terminou em `BUILD_EXIT=0`. As cinco raízes auditadas dependem
somente de `propext`, `Classical.choice` e `Quot.sound`; o verificador
fail-closed `check_stage19_axioms.py` também confirma que não há `sorryAx`.

A primeira compilação do certificado falhou porque o teorema gerado ainda
instanciava a recorrência em `n=18`; o erro de reescrita está preservado em
`state-stage19-build-attempt1.log`. A instância foi corrigida para `n=19`, o
arquivo foi regenerado deterministicamente e a compilação final passou. O log
final contém apenas as cinco raízes esperadas e `BUILD_EXIT=0`.

O wrapper de compilação exige no mínimo 30 GiB de `MemAvailable`. Após o build
foram observados 60.45 GiB disponíveis. Isso documenta a condição desta
execução, não uma garantia sobre outros runners.

## Pins

- Base `main` antes do checkpoint: merge da PR #279, `b06200968bc004694ee8d7acc3af88463d40ebf2`.
- Geometry de referência: `bf76ce8f5bb753b377a12ba6dbd5c397e4fb3fc3`.
- Carry: `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- Lean: `leanprover/lean4:v4.32.0`, commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`.

## Reprodução

Na raiz do checkout, execute:

```bash
research/native-moving-schur-sigma/mission-c5-finite-c2-certification/evidence/rational-boxes/c5-m2-dirichlet-term-stage19-20261107/reproduce.sh
```

O script preserva os logs do probe e do certificado na pasta de evidências e
executa o verificador fail-closed. As fontes e o gerador ficam junto dos logs;
`SHA256SUMS.txt` registra os hashes. A saída `.olean` fica no cache local e não
é necessária no Git.

## Publicação

A PR #280 integrou o commit de prova `8a8fcde` na `main` pelo merge
`de09a348a9e2b0f0c6bd700eeed63d92726a56c5`. O GitHub não reportou checks
hospedados. A integração é apenas um checkpoint parcial e não conclui C5.
