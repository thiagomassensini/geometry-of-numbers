# C5 — certificado parcial do prefixo de 96 entradas da tabela de Bernoulli

## Resultado

`c5BernoulliPrimeTable_96_eq_data` estende a igualdade já integrada para 64
entradas (índices 0–63) até 96 entradas (índices 0–95). A prova usa o
certificado 0–64 como base, a recorrência `bernoulli'_def` nos índices pares
novos e o teorema padrão de que os valores ímpares acima de 1 são zero.

O checkpoint é parcial: 96 das 601 entradas têm igualdade formal certificada;
as outras 505 ainda precisam de provas por blocos. A comparação reprodutível
dos 601 valores da sonda com os literais não substitui essas provas. Esta etapa
não liga nenhuma caixa exportada de zeta à sua avaliação Lean nem prova uma
inclusão da fonte C5.

## Build e auditoria

- Lean 4.32.0, `warningAsError=true`; Mathlib
  `81a5d257c8e410db227a6665ed08f64fea08e997`; Carry
  `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- `reproduce-clean.sh` recompila a sonda, a tabela, o certificado 96 e a
  auditoria isolada em uma saída nova. Usa como dependência o `.olean` limpo do
  certificado 64, já compilado e integrado; a igualdade 96 é recompilada do
  zero. O script compara os 601 valores como racionais e verifica a saída de
  `#print axioms`.
- Reprodução executada: `CLEAN_BUILD=PASS`, `DATA_TABLE_CHECK=PASS`,
  `AXIOM_AUDIT=PASS`. A compilação limpa de 96 terminou em 38m42s, com pico de
  6.45 GiB RSS; `warningAsError=true`. A auditoria retorna somente `propext`,
  `Classical.choice` e `Quot.sound`.
- Resultado e métricas do build limpo ficam em `RESULT.txt`, nos logs
  individuais e em `SHA256SUMS.txt`. As tentativas iniciais, inclusive a
  primeira compilação aprovada, ficam preservadas em `attempts/`.
- Próximo passo: provar 128 entradas (índices 0–127), depois avançar em blocos
  até 601; então retomar a ponte formal de uma caixa de zeta.

## Tentativas preservadas

Logs de build inicial e eventuais correções ficam em `attempts/`. Builds que
falharem ou forem interrompidos são preservados e descritos aqui, sem serem
tratados como certificados válidos.
