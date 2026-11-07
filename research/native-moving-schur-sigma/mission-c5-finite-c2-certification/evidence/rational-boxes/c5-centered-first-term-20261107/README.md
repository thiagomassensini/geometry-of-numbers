# C5 — primeiro termo da cabeça zeta certificado

**Estado:** pequeno subcomponente formal compilado e auditado; C5 ainda incompleta.

## Resultado

[`SigmaC5CenteredFirstTerm.lean`](../../../../SigmaC5CenteredFirstTerm.lean) prova `c5CenteredDirichletTermBox_one_eq_generic`: para qualquer caixa de nó `S` e qualquer entrada `logTwo`, o primeiro termo da cabeça (`m=1`) da soma de Dirichlet é exatamente `c5GenericBox 11 15`. Em `m=1`, `c5CenteredLogQ` zera; a exponencial arredondada com entrada zero reduz ao estágio genérico `k=4`, usando `c5RoundedExpC_zero_stage_2_to_192_closed_form` já provado.

O lema fixo `c5CenteredDirichletTermBox_one_fixed` instancia a definição de produção `c5CenteredLog2I 512`. Isso certifica formalmente o primeiro dos 99 termos da cabeça; não certifica os outros 98, as correções de Euler–Maclaurin, a caixa completa de zeta nem a inclusão dos coeficientes C2. Os resultados O3 seguem condicionais.

## Build e auditoria

- Lean 4.32.0 (`8c9756b28d64dab099da31a4c09229a9e6a2ef35`), Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`, Carry `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- Build passou com `warningAsError=true`, `BUILD_EXIT=0`.
- As duas raízes foram auditadas: somente `propext`, `Classical.choice` e `Quot.sound`; sem `sorryAx`.
- O checker fail-closed está em `check_c5_centered_first_term_axioms.py`; o log e os hashes estão nesta pasta.
- A compilação usou `MemAvailable=63,394,016 KiB`, acima do limite de 30 GiB.
- A saída `.olean` é reproduzível e fica em `.cache`, sem ser versionada.

## Reprodução

Da raiz do checkout Geometry, execute:

```bash
bash research/native-moving-schur-sigma/mission-c5-finite-c2-certification/evidence/rational-boxes/c5-centered-first-term-20261107/reproduce.sh
```

O script verifica os pins Carry/Lean, compila o módulo e executa o checker de axiomas.

## Próximo subproblema

O termo `m=1` é tratado agora. Continuar a prova modular dos demais termos e componentes da caixa centrada, reutilizando as recorrências de Taylor já integradas. Não repetir a tentativa monolítica da igualdade da caixa CSV completa, documentada em `c5-exported-box-proof-attempt/`.
