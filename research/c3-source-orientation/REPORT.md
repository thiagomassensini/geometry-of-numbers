# Da PR #41 e da PR #70 à terceira direção: onde entra o sinal

**Classificação: PARTIAL.** A PR #41 fornece a direção crítica sem hipótese de sinal, e a #70 transporta essa direção ao kernel Bézout da fonte C3. Este trabalho acrescenta, para dimensão três e cada setor, uma fórmula exata do residual em função do último coeficiente novo, com todos os acoplamentos anteriores. Não se demonstra a desigualdade de sinal pela geometria nem uma lei all-order. A prova de sinal finito da PR #144 permanece válida, com sua dependência theta explicitada.

Base: `055f0ff353b0323234501c36891f1377918994b0`, PR #144, empilhada sobre a #143. Os novos lemas não utilizam os resultados theta de #144: a auditoria percorre tipos e corpos, exige as caixas C3 e o transporte de #70 e bloqueia explicitamente as caixas theta e os certificados de sinal listados em `SourceAudit.lean`. Isso não é uma prova semântica de independência de qualquer resultado matematicamente equivalente. As outras branches, arquivos históricos e alterações locais preexistentes não foram alterados.

## A — O que as PRs anteriores fornecem

A #41 constrói ortogonalização algébrica e residual de Schur sob inversibilidade, sem exigir positividade do pivô. A #70 constrói o kernel Bézout da mesma fonte e transporta o residual com o fator exato `c₀²`. Também certifica diretamente, na cabeça C3 reorganizada e em toda uma faixa de direções, a margem da **segunda direção par**. Faz isso com quatro caixas da fonte da #69, `c₀,…,c₃`, e a cauda original; não prova a margem da terceira direção.

A #144 controla HT, TH e TT em cutoff 256 para dimensão três e prova o sinal finito usando intervalos theta. Aqui a pergunta mais específica é o que precisa ser certificado para procurar o sinal diretamente na fonte, sem reutilizar esse sinal como premissa.

## B — O que foi demonstrado agora

Para uma sequência real arbitrária `c`, seja `Bₛ` o bloco Bézout da fonte da #70, `Aₛ` seu prefixo `2×2`, `bₛ` a coluna de cruzamentos até a terceira direção e

\[
 R_s=b_s^TA_s^{-1}b_s.
\]

Não se presume que esse termo tenha sinal positivo. O Lean formaliza as matrizes `B₀` e `B₁` inteiras em `even_three` e `odd_three`; em particular,

\[
\begin{aligned}
(B_0)_{22}&=-5c_0c_5-3c_1c_4-c_2c_3,\\
(B_1)_{22}&=-6c_0c_6-4c_1c_5-2c_2c_4+3c_3^2.
\end{aligned}
\]

Portanto, com os cruzamentos completos `Rₛ` mantidos,

\[
\begin{aligned}
 p_{B,0}&=E_0-5c_0c_5,&E_0&=-3c_1c_4-c_2c_3-R_0,\\
 p_{B,1}&=E_1-6c_0c_6,&E_1&=-4c_1c_5-2c_2c_4+3c_3^2-R_1.
\end{aligned}
\]

`even_source_schur_coefficient` e `odd_source_schur_coefficient` provam essas identidades sem hipótese de positividade nem de inversibilidade; nelas o inverso de matriz de Lean é total. A interpretação como separação da direção crítica e o transporte aos momentos exigem o prefixo invertível.

Sob `c₀>0`, provado para a fonte nativa pelas caixas originais da #70, e com o respectivo prefixo de momentos invertível, `native_even_gate` e `native_odd_gate` estabelecem:

\[
\begin{aligned}
 p_{0,2}>0&\iff c_5<\frac{E_0}{5c_0},\\
 p_{1,2}>0&\iff c_6<\frac{E_1}{6c_0}.
\end{aligned}
\]

São **equivalências exatas, não provas independentes de sinal**. Identificam, no mesmo kernel da fonte, a desigualdade que as estimativas C3 precisam resolver. `even_ceiling_unchanged`/`odd_ceiling_unchanged` provam que os limiares não dependem, respectivamente, de `c₅`/`c₆`; `even_critical_unchanged`/`odd_critical_unchanged` demonstram que a mesma alteração preserva a direção crítica da fonte. Os lemas preservam o bloco e a coluna completos.

## C — Teste de insuficiência, com alcance exato

`even_schur_data_insufficient` e `odd_schur_data_insufficient` constroem controles algébricos com os mesmos primeiros cinco coeficientes no par, ou seis no ímpar, o mesmo prefixo e a mesma coluna de cruzamentos, mas resíduos de sinais opostos ao variar apenas `c₅` ou `c₆`. É um controle sobre a informação algébrica disponível: **não** afirma que os controles sejam outras fontes C3 físicas nem refuta a geometria Carry. Outras relações comprovadas da fonte poderiam impedir essas variações.

Isso explica por que as quatro caixas da #70, sozinhas, não determinam o novo sinal. As identidades não autorizam descartar cauda, mudar métrica, impor positividade nem inferir que a física admite a perturbação.

## D — Diagnósticos, não certificados

`source_threshold_diagnostic.py` calcula apenas a cabeça C3 original em cutoff 256, com mpmath, Gamma/chart e bordo, sem momentos, theta, zeta, zeros ou alturas como entrada. Os valores aproximados são:

| Setor | coeficiente da cabeça | limiar da cabeça | folga |
|---|---:|---:|---:|
| par | `c₅≈−1,4616025760·10⁻¹¹` | `≈−1,4604943530·10⁻¹¹` | `≈1,1082·10⁻¹⁴` |
| ímpar | `c₆≈4,2745400455·10⁻¹⁴` | `≈4,2752096487·10⁻¹⁴` | `≈6,6960·10⁻¹⁸` |

São leituras numéricas da cabeça finita, **não intervalos provados para os coeficientes completos** nem teoremas sobre a cabeça. Os coeficientes pares do jet finito são calculados como complexos; sua realização efetivamente real nessa simulação não é apresentada como prova Lean de que a cabeça é real.

`evaluate_boxes.py` é uma simulação racional de condicionamento com centros obtidos do mesmo diagnóstico, `c₄,c₅,c₆` idealizados como valores pontuais e uma tolerância comum hipotética para `c₀,…,c₃`. Com `10⁻¹²` o intervalo calculado cruza zero em ambos setores; com `10⁻¹⁵` não cruza nessa simulação. Isso não estabelece tolerância suficiente na fonte: as caixas de `c₄,…,c₆`, o erro da cabeça e a cauda ainda não foram incluídos.

## E — Próxima obrigação e validação

A #69 certifica os jets até ordem 6 da variável original, que cobrem `c₀,…,c₃`. Para alcançar `c₅` e `c₆`, a rota direta requer jets até ordens 10 e 12, respectivamente, com os fatores originais Gamma, chart, prefixo C3 e bordo; é necessário controlar também a precisão dos coeficientes anteriores e as operações de inversão no limiar completo. A cota da cauda C3 de #144 já trata os coeficientes até índice 6 em cutoff 256. O próximo passo é estender as caixas nativas dos fatores/cabeça até esses jets e provar **uma das desigualdades acima** por intervalos, sem usar as caixas theta como origem do sinal. Para provar a margem da própria cabeça, será necessário estabelecer o crosswalk adequado para os coeficientes complexos da cabeça e controlar os três termos de cauda; este relatório não presume que ela seja real.

No host `llm`, com os caches de #70 e da cadeia anterior:

```bash
bash research/c3-source-orientation/validate.sh
lake build --wfail
bash scripts/audit-foundation.sh
bash scripts/audit-geometry.sh
bash scripts/audit-analysis.sh
/home/thlinux/miniforge3/bin/python research/c3-source-orientation/source_threshold_diagnostic.py
python3 research/c3-source-orientation/evaluate_boxes.py
```

Os módulos de pesquisa são compilados com warnings como erros, `#print axioms` e auditoria transitiva. Os logs estão em `evidence/`; dependências anteriores são reutilizadas dos `.olean` existentes e não se reivindica reconstrução limpa dos repositórios dependentes. Não foram introduzidos `sorry`, `admit`, `native_decide` ou axiomas novos.
