# C5 — certificado parcial do prefixo de 192 entradas da tabela de Bernoulli

## Escopo

Esta etapa estende `c5BernoulliPrimeTable_160_eq_data` para os índices 0–191,
com `c5BernoulliPrimeTable_192_eq_data`. O resultado só conta como validado
depois de compilação limpa e auditoria isolada dos axiomas. Mesmo com sucesso,
192 das 601 entradas estarão certificadas; 409 permanecerão abertas. A ponte
CSV–Lean das caixas de zeta, as inclusões da fonte C2 e os sinais finais seguem
como obrigações separadas.

## Ambiente fixado

- Lean 4.32.0, toolchain commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`;
  Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`.
- Geometry reference `bf76ce8f5bb753b377a12ba6dbd5c397e4fb3fc3`; Carry
  `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- O prefixo 160 foi integrado pela PR #312, merge
  `cb829d98d799df72f07c9aff03e9d93871da6f77`.
- A reprodução importa o `.olean` compilado de 160 entradas via
  `C5_PREFIX160_CACHE` e reutiliza os caches certificados de 128, 96 e 64.
  Cada caminho pode ser substituído por variável de ambiente.

## Reproduzir

```bash
bash research/native-moving-schur-sigma/mission-c5-finite-c2-certification/evidence/rational-boxes/c5-bernoulli-data-prefix192-20261108/run-detached.sh
```

Consulte `runner-status.txt` e `run-state.txt` para acompanhar a execução. O
processo compila a prova e o módulo de auditoria em uma pasta de saída nova,
registra tempos e pico de RSS, verifica os axiomas e grava hashes. Não relance
enquanto `runner-status.txt` estiver `RUNNING`.

## Resultado

Pendente. Até o build e a auditoria passarem, o estado formal integrado segue
em 160/601. Esta etapa não prova as caixas da fonte C2 nem os sinais finais.
