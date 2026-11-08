# C5 — certificado parcial do prefixo de 128 entradas da tabela de Bernoulli

## Resultado

`c5BernoulliPrimeTable_128_eq_data` estende a igualdade formal integrada para
96 entradas (índices 0–95) até 128 entradas (índices 0–127). Usa o certificado
de 96 entradas como base, a recorrência `bernoulli'_def` nos índices pares
novos e o teorema de que os valores ímpares de Bernoulli acima de 1 são zero.

O checkpoint é parcial: 128 das 601 entradas têm igualdade formal certificada;
as outras 473 seguem abertas. A comparação reprodutível dos 601 valores da
sonda com os literais não substitui essas provas. A ponte entre caixas de zeta
exportadas e sua avaliação Lean, bem como as inclusões da fonte C5, continuam
abertas.

## Build e auditoria

- Lean 4.32.0 (toolchain commit
  `8c9756b28d64dab099da31a4c09229a9e6a2ef35`), `warningAsError=true`; Mathlib
  `81a5d257c8e410db227a6665ed08f64fea08e997`; Geometry reference
  `bf76ce8f5bb753b377a12ba6dbd5c397e4fb3fc3`; Carry
  `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`. The integrated base certificates
  are prefix 64 at `509e773d44c25aa43cb1d8bd32d1b9645331ae04` and prefix 96 at
  `4fc4c8d7037a80323e0382fb5e228015a876f99a`.
- `reproduce-clean.sh` compila sonda, tabela, certificado 128 e auditoria
  isolada em uma saída nova. Importa os `.olean` limpos dos certificados 96 e
  64, integrados pelas PRs #302 e #300. Também compara os 601 valores como
  racionais e verifica `#print axioms`.
- Resultado: `CLEAN_BUILD=PASS`, `DATA_TABLE_CHECK=PASS` para 601 coeficientes,
  `AXIOM_AUDIT=PASS`. O teorema usa apenas `propext`, `Classical.choice` e
  `Quot.sound`.
- Os quatro módulos terminaram com `BUILD_EXIT=0`. Tempos e picos RSS: sonda
  1m56.99s / 2,683,564 KiB; tabela 16.35s / 2,706,148 KiB; certificado
  1h15m45s / 9,450,592 KiB (cerca de 9.01 GiB); auditoria 6.59s / 3,282,880
  KiB. Os quatro logs, os resultados da comparação e da auditoria estão nesta
  pasta.
- Os hashes de fontes, logs, reprodução, verificadores e resultado estão em
  `SHA256SUMS.txt`.

## Tentativas preservadas

Logs de builds iniciais, erros e correções ficam em `attempts/`. A primeira
execução não incluiu o cache transitivo 64 no caminho de imports e parou com
`unknown module prefix 'SigmaC5BernoulliDataCertificate64'`; o script foi
corrigido para importar os caches 96 e 64. A reprodução seguinte alcançou a
prova, mas o simplificador atingiu o padrão de 100000 passos em 33 casos do
bloco; o log também mostra `sorryAx` gerado pela recuperação após erros, então
essa execução não é válida como certificado. A prova agora eleva o limite de
passos para 200000 e será recompilada. Esses dois logs são preservados em
`attempts/`; tentativas interrompidas ou com erros nunca contam como
certificado válido. A reprodução corrigida com `maxSteps := 200000` passou e
é a única execução contabilizada como prova. O build final auditado não contém
`sorryAx`.

## Próximo passo

Este checkpoint localiza a prova apenas nos dados: 128 das 601 entradas agora
têm igualdade formal; 473 continuam abertas. Ele não prova as caixas de zeta,
as inclusões da fonte C5 nem os sinais finais. A próxima prova é o prefixo 160,
usando este prefixo 128 como base; C5 permanece incompleta.
