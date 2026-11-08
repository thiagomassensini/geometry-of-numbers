# C5 — prefixo Bernoulli 192 validado (resultado parcial)

## Escopo e estado

`CarrySigmaObstruction.c5BernoulliPrimeTable_192_eq_data` estende o
certificado integrado do prefixo 160 aos índices 0–191. A compilação limpa e a
auditoria isolada passaram. O resultado ainda aguarda PR e merge; o último
prefixo integrado na `main` continua sendo 160.

São 192 das 601 entradas certificadas nesta branch; 409 continuam abertas. A
ponte CSV–Lean das caixas de zeta, as inclusões `sigmaC00495SourceBoxes` e
`sigmaC01SourceBoxes`, a composição com a fonte original e os sinais finais
seguem pendentes. Este checkpoint não certifica os sinais C2.

## Ambiente fixado

- Lean 4.32.0, toolchain commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`;
  Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`.
- Geometry reference `bf76ce8f5bb753b377a12ba6dbd5c397e4fb3fc3`; Carry
  `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- Base `main`: `605c55e899d62a658bed511d13be3b95b09840c8`; prefixo 160
  integrado pela PR #312, merge `cb829d98d799df72f07c9aff03e9d93871da6f77`.
- A reprodução importa o `.olean` certificado de 160 entradas via
  `C5_PREFIX160_CACHE` e reutiliza os caches certificados de 128, 96 e 64.
  Cada caminho pode ser substituído por variável de ambiente.
- Prova: commit `636ea8d7ceea1af08adafcdb4d373e8e9b9895b4`;
  checkpoint com launcher e estado: `4da3b00f4e2ae510b303f79595acaa4afdac58ef`.
- Branch `codex/c5-zeta-bernoulli-prefix192-20261108`; PR ainda não aberta.

## Resultado de validação

- `CLEAN_BUILD=PASS`, `AXIOM_AUDIT=PASS`, `EXIT=0`.
- A declaração auditada depende somente de `propext`, `Classical.choice` e
  `Quot.sound`; o auditor rejeita `sorryAx` e `native_decide`.
- Lean 4.32.0 com `warningAsError=true`; compilação limpa em 3h07m38s,
  pico RSS 16,632,976 KiB. Auditoria isolada em 4.40s, pico RSS 3,236,712 KiB.
- SHA-256 do arquivo da prova:
  `dc81863af236d296e084cdf65a002728be82a87f47c83704928fda1756e5e0a8`.
- Logs, runner finalizado, estado da execução, resultado e hashes estão neste
  diretório. Verifique os artefatos com `sha256sum -c SHA256SUMS.txt`.

## Reproduzir

```bash
bash research/native-moving-schur-sigma/mission-c5-finite-c2-certification/evidence/rational-boxes/c5-bernoulli-data-prefix192-20261108/run-detached.sh
```

O processo compila a prova e o módulo de auditoria em uma pasta nova, registra
tempos e pico de RSS, verifica os axiomas e grava hashes. A execução registrada
terminou; uma reprodução nova é opcional. Não contar o resultado como integrado
até o merge da PR.
