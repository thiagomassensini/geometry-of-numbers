# C5 — certificado parcial do prefixo 0–64 da tabela de Bernoulli

## Resultado

`c5BernoulliPrimeTable_64_eq_data` estende a igualdade já integrada do prefixo
de 32 entradas até 64 entradas (índices 0–63). A prova identifica cada valor com a recorrência de Bernoulli;
usa a igualdade do prefixo 0–32 como base, a recorrência `bernoulli'_def` nos
índices novos e o teorema padrão de que os valores ímpares acima de 1 são zero.
No build limpo, o certificado 0–64 passou em Lean 4.32 com warnings como erros
em 14:09, com pico de RSS de aproximadamente 4.8 GiB. A auditoria isolada
reporta somente `propext`, `Classical.choice` e `Quot.sound`.

Este checkpoint continua parcial: 64 das 601 entradas (índices 0–63) têm
igualdade formal certificada; as outras 537 ainda precisam de provas por
blocos. A
comparação racional reprodutível de todos os 601 valores com a sonda não
substitui essas igualdades formais. Nenhuma caixa de zeta ou inclusão da fonte
C5 é concluída aqui.

## Build e auditoria

- Lean 4.32.0, `warningAsError=true`; Mathlib em
  `81a5d257c8e410db227a6665ed08f64fea08e997`; Carry em
  `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- `reproduce-clean.sh` recompila a sonda, a tabela, os certificados dos
  prefixos 32 e 64 e a auditoria isolada; compara os 601 valores como
  racionais e verifica a saída de `#print axioms`.
- O resultado, as métricas do build limpo, os pins e os hashes ficam em
  `RESULT.txt`, nos logs individuais e em `SHA256SUMS.txt`.
- Próximo passo: provar o prefixo 96 usando 0–64 como base e avançar em blocos
  até 601; depois retomar a ponte formal de uma caixa de zeta.

## Tentativas preservadas

- `attempts/SigmaC5BernoulliDataCertificate64-initial-build.log` registra a
  tentativa por igualdade cumulativa de arrays, interrompida manualmente após
  10:17 sem erro Lean e sem produzir o certificado.
- `attempts/prefix64-scalar-build.log` preserva os primeiros erros de tipos e
  denominadores da formulação escalar.
- `attempts/prefix64-scalar-v2-build.log` registra que a redução aritmética
  terminou após 13:49, mas a orientação da igualdade entre os prefixos 32 e 64
  impediu a compilação final.
- A fonte atual corrige a orientação e a validação limpa completa será
  registrada separadamente.
