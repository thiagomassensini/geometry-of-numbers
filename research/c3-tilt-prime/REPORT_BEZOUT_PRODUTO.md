# Produto de Bézout, resposta logarítmica e objetos Green

**Resultado: PARTIAL.** O teste simbólico trazido pelo usuário foi reproduzido e uma lei geral de produto do kernel de Bézout foi demonstrada em Lean, incluindo o transporte exato dos blocos de qualquer dimensão nos dois setores. A igualdade é algébrica e não demonstra positividade da fonte canônica, identidade de estados ou Gram física de Green.

## Convenção e objetos

A fonte completada na altura é `F(z)=F(0)Φ(z²)`, perto do centro, com `Φ(0)=1`. Na convenção `Q₋(z)=−F′(z)/(2F(z))` já usada nos módulos de Green/TFVD,

\[
Q_-(z)=zq(z^2),\quad q(u)=-\Phi'(u)/\Phi(u)=\sum_n h_nu^n.
\]

A convenção `Q₊=F′/(2F)` proposta na mensagem é igualmente legítima, mas então `Q₊=−z∑h_nz^{2n}` para os mesmos momentos. O sinal das identidades polarizadas deve ser transportado junto. O teorema anterior `fullTransverse_eq_normalizedGreen` usa `Q₋` e fornece `T=2iFQ₋=−2iFQ₊`. Nenhuma alteração de fonte ou de momentos é feita para trocar convenção.

A igualdade existente `canonicalC3BracketTfvdNormalizedResponse_eventuallyEq_completed` identifica o **readout escalar** da síntese TFVD/Wronskiano com `Q₋` perto do centro; ela não afirma que a Gram física de Green seja a matriz de Hankel canônica. `normalizedCompletedGreenState_polarizedResponse` fornece uma relação polarizada **condicional** a `HasDivisionFreeGreenRepresentationOn` e às condições de não anulação especificadas. A representação física e suas hipóteses não são substituídas por uma igualdade numérica de coeficientes.

Separadamente, `SourceBezout.source_kernel_even`, `source_kernel_odd` e `SourceNative.native_source_bezout_congruence` demonstram que o kernel formal de Bézout, construído da característica reduzida, está ligado às Hankel canônicas por congruência triangular. `native_source_bezout_posSemidef_iff` e `native_source_bezout_posDef_iff` são equivalências, não provas incondicionais de sinal. Bézout formal, Gram física Green e Hankel são objetos tipados diferentes; uma congruência ou transporte efetivo pode relacioná-los, mas não autoriza igualá-los por definição.

## Nova identidade Lean

Para séries formais arbitrárias `C,D` sobre um domínio integral comutativo, denotando por `B_s` o kernel `sourceKernel` no setor `s`, `sourceKernel_product` prova em duas variáveis e em todas as ordens:

\[
B_s(CD)(u,v)=D(u)D(v)B_s(C)(u,v)+C(u)C(v)B_s(D)(u,v).
\]

`sourceKernel_product_block` extrai exatamente, para todo tamanho `r`,

\[
[B_s(CD)]_r=T_r(D)[B_s(C)]_rT_r(D)^T+
T_r(C)[B_s(D)]_rT_r(C)^T,
\]

onde `T_r` é `convolutionMatrix`. As identidades valem nos setores original e deslocado, não exigem inverses, positividade, zeros ou ajuste de coeficientes. `coefficient_transport` prova o transporte para **qualquer** kernel formal de duas variáveis. A prova usa a regra de Leibniz e o lema existente `bezout_numerator`; preservar as duas parcelas conserva todos os cruzamentos dos blocos.

Para aplicar a decomposição como cabeça e correção da fonte Carry, ainda é preciso identificar o produto com os fatores concretos e controlar o segundo termo na mesma direção crítica. A lei por si só não atribui sinal ao segundo termo; positividade da cabeça não controla o bloco completo.

## Teste exato fornecido

O script `teste_bezout_produto_exato.py` foi reproduzido localmente com SymPy, e preservado sem alterações. Para `C=1−u−u²`, `H=1−u+u²/8` e `D=C/H`, o kernel original fornece

\[
[B_0(H)]_2=\begin{pmatrix}1&-1/4\\-1/4&1/8\end{pmatrix},\quad
[B_0(C)]_2=\begin{pmatrix}1&2\\2&-1\end{pmatrix}.
\]

Os determinantes são `1/16` e `−5`. Na direção `e₂`, os termos transportados valem `1/8` e `−9/8`, totalizando `−1`. É um contraexemplo **exato no modelo racional escolhido**, não um contraexemplo à fonte Carry. A identidade de produto e a decomposição por blocos foram provadas genericamente em Lean; os valores específicos do exemplo foram verificados pelo SymPy, não formalizados em Lean.

O relatório adicional sobre escala distingue corretamente os coeficientes canônicos de momentos da norma vertical material. Suas conclusões de assíntota por zeros, Prony e comparações numéricas não foram reexecutadas nem usadas na prova; em particular, não entram como premissas sobre positividade ou sobre a fonte geométrica.

## Validação e próxima obrigação

Base `46817610bac12312dab48c8e2e12b39252cce786`, branch `agent/c3-critical-tilt-prime`, PR #146 empilhada na #145. A prova nova está em `BezoutSourceProduct.lean`; seus teoremas impressos dependem apenas de `propext`, `Classical.choice`, `Quot.sound`. `BezoutSourceProductAudit.lean` inclui as raízes anteriores de proveniência, mais as novas. A auditoria bloqueia explicitamente consumidores de sinais e de caixas theta nomeados; não equivale a uma inspeção semântica de todas as possíveis equivalências.

```bash
bash research/c3-tilt-prime/validate_bezout_product.sh
lake build --wfail
bash scripts/audit-foundation.sh
bash scripts/audit-geometry.sh
bash scripts/audit-analysis.sh
```

O teste simbólico foi executado na máquina local, onde SymPy já estava instalado; a versão e o hash estão em `evidence/bezout-product-python.log`. O build Lean usa os caches declarados na branch e não é um rebuild limpo das dependências externas. Os registros estão em `evidence/`.

Próxima obrigação: identificar sem circularidade os fatores **concretos** cabeça e correção da fonte completada, transportar sua identidade de produto até a mesma direção física crítica com os dois argumentos independentes e controlar a contribuição do termo corretivo, inclusive bordos e cauda. A desigualdade necessária deve ser demonstrada a partir da fonte, não ser apenas a positividade de Hankel renomeada.
