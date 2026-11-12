# Lei de compensação por ordem para Bézout e TFVD

**Classificação: PARTIAL — núcleo algébrico e transporte exato ao TFVD formalizados; os sinais gerais e as margens C3 independentes continuam abertos.** Nenhuma positividade all-order foi inferida da equivalência de Schur.

## A. Origem e proveniência

Repositório: `thiagomassensini/geometry-of-numbers`. Branch: `agent/tfvd-bezout-order-compensation-20261110`. Base: `origin/main` em `8f5631a7808ad7c73491b558a894566e1d39899c`. Pins reutilizados: Lean `v4.32.0`, mathlib `81a5d257c8e410db227a6665ed08f64fea08e997` e GreenFrame `cd2d838bee67ad23f869a02f8ed9f0a0feb926fa`.

PRs #41, #69, #70, #143, #144 e #145 já estavam integradas à base. A origem geométrica, o bracket C3, a completion, a câmera e os fatores não foram alterados. O kernel Bézout e sua congruência foram importados de `research/tfvd-bezout-schur-residual/SourceBezout.lean`; as estimativas de coeficientes mistos e da cauda vieram de `KernelBudget.lean`, `LiteralTailBounds.lean` e `LiteralBudgetLimit.lean`; a decomposição literal e a repartição foram reutilizadas de `LiteralTfvd.lean`, `Repartition.lean` e `NativeRepartition64.lean`.

## B. Resultados demonstrados em Lean

Os módulos novos estão em `research/tfvd-bezout-order-compensation/`.

- `CoefficientLaw.lean`: fórmulas explícitas par/ímpar dos coeficientes dos kernels e lema de dependência por prefixo, derivadas de `mixed_kernel_coefficient` já existente.
- `RankOneUpdate.lean`: `sourceBezout_lastCoefficient_rankOne` prova, para qualquer sequência real, ordem, setor e incremento, que só a última diagonal muda.
- `Regression.lean`: os blocos 2×2 e as diagonais 3×3 das duas torres conferem com as fórmulas-alvo; o controle sintético `1-u-u²` continua não semidefinido positivo.
- `BorderedDeterminant.lean`: `det_add_lastCoordinateMatrix` e `sourceBezout_borderedDet_lastCoefficient` provam a lei de determinante sem supor invertibilidade do prefixo.
- `SchurThreshold.lean`: o prefixo antigo e o acoplamento são invariantes; o Schur é afim no último coeficiente; `sourceBezout_lastCoefficient_threshold` é uma equivalência sob `c₀>0`. `nativeSource_pivot_iff_source_threshold` também requer prefixo nativo invertível e `c₀>0` explícitos.
- `TfvdBoundaryLaw.lean`: igualdade exata do jet complexo cabeça+cauda, transporte para a lei do determinante e regra suficiente de compensação sob uma cota absoluta da cauda.
- `FiniteC3Gate.lean`: usa a cota original C3/256 da cauda e especializa a regra suficiente aos dois terceiros determinantes, mantendo a margem de cabeça como hipótese aberta.
- `Audit.lean`: aplica a asserção automática de pegada padrão e imprime `#print axioms` para os 37 teoremas públicos novos.

As dependências dos teoremas novos listadas por `#print axioms` são somente `propext`, `Classical.choice` e `Quot.sound`. Não foram introduzidos `sorry`, `admit`, `native_decide` ou axiomas.

## C. Lei geral por ordem

Para `s=0` (setor ordinário) ou `s=1` (deslocado), no bloco de tamanho `n+1`, seja `m=2n+s+1`. `sourceBezout_lastCoefficient_rankOne` formaliza

\[
B_{s,n+1}(c+\delta e_m)=B_{s,n+1}(c)-m c_0\delta E_{nn}.
\]

Todos os coeficientes anteriores ficam fixos. `sourceBezout_oldPrefix_unchanged` e `sourceBezout_oldCoupling_unchanged` explicitam a invariância do prefixo e da coluna de acoplamento. As regressões confirmam os termos novos `−5c₀c₅` e `−6c₀c₆` nas diagonais finais par e ímpar.

Sem inversa, o determinante satisfaz

\[
\det B_{s,n+1}(c)=J_{s,n}(c)-m c_0\det(B_{s,n}(c))c_m,
\]

onde a definição formal `sourceBezoutLastCoefficientRemainderDet` toma `J` como o determinante do bloco após zerar somente `c_m`. A identidade vale mesmo quando o prefixo é singular. A expansão equivalente de `J` como `det(A)d^{<}-b^T\operatorname{adj}(A)b` ainda não foi formalizada nesta branch; essa obrigação está registrada, sem ser presumida no relatório como teorema Lean.

Se o prefixo é invertível, `sourceSchur_lastCoefficient_update` dá

\[
p_{B,s,n}(c+\delta e_m)=p_{B,s,n}(c)-m c_0\delta.
\]

Com `c₀>0`, o limiar é `p(c)>0 ↔ c_m<p(c^{(m,0)})/(m c₀)`. Para a fonte nativa, `sourceSchur_eq_scaled` preserva `p_B=c₀²p_H`; `nativeSource_lastCoefficient_threshold` e `nativeSource_pivot_iff_source_threshold` não confundem esse fator com a identidade distinta do resto nativo `p_B=c₀·nativeSourceSchurRemainder`.

## D. Lei TFVD de compensação de fronteira

`literal_head_tail` prova a igualdade complexa exata da fonte completada. Só depois dessa igualdade, `nativeC_coefficient_eq_literal_head_tail` toma partes reais e obtém `c_m=Re H_M(m)+Re T_M(m)`. O determinante se transporta exatamente para

\[
\det B_{s,n+1}=J_{s,n}-m c_0D_{s,n}\Re H_M(m)-m c_0D_{s,n}\Re T_M(m),
\qquad D_{s,n}=\det B_{s,n}.
\]

Os quatro cruzamentos ordenados `HH`, `HT`, `TH`, `TT`, os dois cutoffs independentes e o pareamento bilinear complexo são preservados pela identidade `native_residual_four_terms_boundary_repartition`, que reutiliza `coefficientPair_four_terms`, `coefficientPair_boundary_repartition` e `native_residual_repartition`. Nenhum cruzamento é descartado e não há identificação com uma Gram hermitiana.

`sourceBoundary_compensation_sufficient` prova a regra condicional geral: se `m,c₀,D>0`, `|t|≤ε` e `J−m c₀D·head>m c₀Dε`, então `J−m c₀D·head−m c₀D·t>0`. `nativeSource_borderedDet_pos_of_boundary_margin` a aplica à fonte literal. A desigualdade estrita da cabeça é a obrigação aberta; a equivalência do limiar não a demonstra.

## E. Certificações da fonte C3

**Setor par (`s=0,n=2`): PARTIAL.** `FiniteC3Gate.lean` prova que a cota original de cauda `|(T₂₅₆(5)).re|≤10⁻²⁰`, `c₀>0`, `D_{0,2}>0` e a desigualdade exata

\[
J_{0,2}-5c_0D_{0,2}\Re H_{256}(5)>5c_0D_{0,2}\,10^{-20}
\]

implicam `det B_{0,3}>0`. A caixa independente da cabeça até o jet 10 não foi obtida.

**Setor deslocado (`s=1,n=2`): PARTIAL.** Analogamente, `|(T₂₅₆(6)).re|≤10⁻²⁰` e

\[
J_{1,2}-6c_0D_{1,2}\Re H_{256}(6)>6c_0D_{1,2}\,10^{-20}
\]

implicam `det B_{1,3}>0`; falta a caixa independente da cabeça até o jet 12.

As duas cotas de cauda foram compiladas a partir de `C3Tail256.lean`, que deriva o limite de Cauchy da cauda acelerada C3 original. Não foi importado `c3_256_critical_positive_of_head` nem qualquer conclusão theta de sinal para provar as margens. O diagnóstico numérico existente da cabeça C3/256, que não é certificado, reporta folgas aproximadas `1.1082230036570294256·10⁻¹⁴` (par) e `6.6960312586855168797·10⁻¹⁸` (ímpar). Essas aproximações não foram usadas em provas. Nenhum coeficiente `c₄,c₅,c₆` foi tratado como intervalo Lean certificado nesta branch.

## F. Contraexemplos e limitações

`regression_negative_control` mantém o controle algébrico `C(u)=1-u-u²`: a recorrência logarítmica e o kernel são compatíveis, mas um bloco Bézout não é semidefinido positivo. Portanto a lei estrutural não impõe sinal para fontes arbitrárias. Alternância de sinais de coeficientes, congruência de positividade e limiar de Schur não foram usados como provas de sinal.

A lei de estabilidade de Schur sob perturbação, a crosswalk da válvula projetiva, a interface com cofatores e a identidade explícita de adjugata para `J` não foram implementadas. Também não foi demonstrada positividade all-order nem uma Gram física positiva.

## G. Obrigações ainda abertas

1. Provar, sem hipótese de sinal circular, as margens exatas de cabeça nos dois gates C3; isso requer caixas verificadas para os jets 10 e 12 da síntese original e propagação intervalar dos coeficientes e acoplamentos anteriores.
2. Formalizar a expressão adjugata de `J` para conectar a constante do determinante zeroado à forma bordada padrão.
3. Auditar transitivamente as dependências de todos os resultados numéricos da fonte antes de qualquer alegação GREEN.

Nenhum desses itens é alegado como concluído. O limite uniforme TFVD de PR #143 continua sendo convergência por ordem fixa, não positividade uniforme.

## H. Validação

Ambiente Lean `v4.32.0`; a execução final de `bash research/tfvd-bezout-order-compensation/validate.sh` terminou com código zero e `-DwarningAsError=true`. O script constrói as dependências auxiliares originais (`CPFormal`, `CarryGeometry`, `NativeCarrySpectralWeyl`, `GreenFrame` e o alvo do operador), recompila a cadeia PR #70 necessária e `C3Tail256`, e compila explicitamente todos os módulos desta missão, incluindo `Audit.lean`. A auditoria usa `#assert_standard_axioms` para rejeitar axiomas fora de `propext`, `Classical.choice` e `Quot.sound` e imprime `#print axioms` para cada um dos 37 teoremas públicos auditados. `lake exe cache get` baixou zero arquivos, usando 6.044 artefatos do pin já disponíveis; `lake build --wfail` passou com **8.850 jobs**. Também passaram `bash scripts/audit-foundation.sh`, `bash scripts/audit-geometry.sh` e `bash scripts/audit-analysis.sh`; suas saídas foram registradas em `/tmp/tfvd-audit-{foundation,geometry,analysis}.log`. A auditoria de análise declara explicitamente que permite os axiomas padrão e não é axiom-free. `git diff --check` passou após as edições de consolidação. `python3 research/c3-source-orientation/source_threshold_diagnostic.py` foi executado apenas como diagnóstico; seu próprio status registra `diagnostico_nao_intervalar`.

Os módulos desta missão em `research/` não fazem parte dos 8.850 jobs do build raiz; sua compilação explícita é coberta separadamente por `validate.sh`. Os logs temporários das auditorias foram mantidos fora do repositório. A PR [#316](https://github.com/thiagomassensini/geometry-of-numbers/pull/316) foi mesclada em 2026-11-12; SHA do merge: `9774ddd42616ad12b9e9a2b9ad93aa89cb7ee796`. Não havia checks reportados, `main` estava sem proteção de branch e a PR estava limpa/mergeável.

Commits publicados: `033b669` (lei dos coeficientes), `78933af` (update de posto um), `69cb7ee` (determinante e Schur), `10aa06a` (TFVD), `73c9cdc` (gates C3 condicionais, auditoria automatizada e validação) e `7fffbd7` (relatório/checkpoint). A sincronização final do SHA de merge foi registrada no commit documental deste acompanhamento; os commits de checkpoint estão em `CHECKPOINT.md`.

## I. Próxima missão mínima

Certificar por intervalos os jets originais da cabeça C3 até as ordens 10 e 12 e provar as duas desigualdades de margem exatas acima, sem usar os sinais theta dos pivôs como premissa.
