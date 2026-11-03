# Prefixo ímpar C3: oitavo jet e margem da fonte

**PASS no prefixo finito; PARTIAL para a terceira direção.** A fonte C3 completada, com bordo e cauda originais, fornece

\[ c_4\le4\cdot10^{-9},\qquad \det B_{1,2}>9\cdot10^{-17},\qquad \operatorname{IsUnit}(K_2). \]

A margem pertence ao **determinante Bézout da fonte**, não a um pivô nem a um autovalor de K₂. Não foram demonstrados o sinal da terceira direção ou uma lei all-order.

## Proveniência e PRs #41 e #70

A #41 fornece a direção de Schur e sua ligação ao bordo original sob inversibilidade, sem pressupor positividade. A #70 fornece o kernel Bézout, a congruência com os momentos, a síntese TFVD completada e a repartição exata do bordo C3 em 64 células.

`odd_original_four_terms` conserva, para dois vetores reais independentes, HH, HT, TH e TT. Cabeça e cauda provêm do mesmo par TFVD completado, incluindo Gamma, chart, fases e bordo. A leitura de coeficientes ocorre depois da síntese e da recomposição. A prova do determinante usa caixas dos coeficientes da fonte recomposta: não certifica separadamente uma desigualdade HH > HT + TH + TT. O pareamento Bézout é bilinear; não foi identificado com uma Gram física de Hilbert.

## O novo jet

- `gamma_coefficient_seven_box` e `gamma_coefficient_eight_box` verificam por aritmética racional exata os dois coeficientes adicionais do avaliador Gamma finito. Seus centros não definem a fonte.
- `native_gamma_nine_boxes` estende as caixas da Gamma original aos jets 0…8, com erro ≤ 10⁻¹⁸. O teorema anterior `native_gamma_jet_error` controla o resto.
- `head_evaluator_check9` verifica os boxes racionais da cabeça nas ordens 7 e 8, reutilizando os anteriores. A cabeça mantém 64 células C3 e o bordo original de 12 endereços.
- `head8_rational_upper` e `gamma_jet_replacement_error9` provam `regrouped_head64_four_upper`: Re H₆₄,₄ ≤ 3999/10¹². A aproximação finita é no máximo 3993/10¹², com erro Gamma 64 Σ(j=0…8)4ʲ/10¹⁸.
- `odd_tail_four_bound` reutiliza o limite da cauda acelerada de toda ordem: ‖T₆₄,₄‖ ≤ 2·10⁻¹⁵. A identidade `regrouped_source` combina os dois termos e prova `native_c4_upper_from_completed_c3`.

As verificações de inclusão e sinal são racionais e checadas pelo kernel; nenhum número de ponto flutuante é premissa.

## Determinante, cruzamento e gate

Defina a=c₁²−2c₀c₂, b=c₁c₂−3c₀c₃ e d=2c₂²−2c₁c₃−4c₀c₄. O bloco ímpar original é [[a,b],[b,d]]. As quatro caixas C3 preexistentes e c₄≤4·10⁻⁹ implicam `odd_source_det_margin_from_completed_c3`: ad−b²>9·10⁻¹⁷. O termo b², que contém o cruzamento, permanece na prova.

`odd_c4_ceiling_from_completed_c3` descarrega c₄<L₄; `odd_prefix_isUnit_from_completed_c3` descarrega a invertibilidade de K₂ sem usar o certificado theta de K₆. `third_odd_gate_from_completed_c3` prova a equivalência

\[ 0<\operatorname{sourceMomentSchur}(h,1,2) \Longleftrightarrow c_6<\frac{\operatorname{oddSourceCeiling}(c)}{6c_0}. \]

A desigualdade à direita **continua aberta nesta rota**. O resultado do prefixo já era conhecido por theta; aqui sua proveniência é C3 completada.

## Diagnóstico e auditoria

`diagnose_odd_head.py` avalia a mesma cabeça e bordo com mpmath, sem theta, zeta, zeros, alturas ou momentos. A menor direção da parte real da cabeça foi aproximadamente 2,56556·10⁻¹¹ e um orçamento numérico conservador dos três termos restantes, 3,64620·10⁻¹⁵. É diagnóstico, não a prova Lean.

`FinalAudit.lean` audita transitivamente 21 raízes, exige as caixas C3, a recorrência e o transporte Schur, e rejeita os consumidores theta e de sinal explicitamente enumerados. Isso não é uma auditoria semântica de toda possível codificação de theta. Os únicos axiomas permitidos são `propext`, `Classical.choice` e `Quot.sound`; não há `sorry`, `admit`, `native_decide` ou novos axiomas.

## Reprodução e próximo passo

No host `llm`, com caches históricos da #70, #145 e #146:

```bash
bash research/c3-odd-head-source/validate.sh
lake build --wfail
bash scripts/audit-foundation.sh
bash scripts/audit-geometry.sh
bash scripts/audit-analysis.sh
```

`CARRY_PR70_ROOT`, `CARRY_PR143_CACHE`, `CARRY_PR145_CACHE` e `CARRY_PR146_CACHE` selecionam caches equivalentes. As dependências `.olean` anteriores são reutilizadas; não se afirma um build limpo dos repositórios externos. Logs e hashes ficam em `evidence/`.

Próximo alvo: estender a Gamma, a cabeça C3 e a cauda aos jets 10 e 12 para controlar c₅ e c₆ e testar os gates da terceira direção, com os cruzamentos. Uma lei all-order ainda exige controle da margem e da cauda dependente da ordem e do setor.
