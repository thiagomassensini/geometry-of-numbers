# Balanço de Euler da direção crítica e orientação de sinal na fonte

**Resultado: PARTIAL.** Há uma nova identidade em toda ordem que cancela os cruzamentos de Euler superiores pela relação de Schur, conserva o residual antigo e transporta o resultado às energias do bordo nativo. A fonte original também certifica o sinal negativo da curvatura sigma na segunda direção par. A desigualdade necessária em toda ordem permanece aberta; um controle exato refuta sua dedução apenas de positividade de entradas, prefixos e recorrência finita.

## A — Base e proveniência

Base: `geometry-of-numbers`, commit `e058b128f31a8155f4d7df02c0a10b56c6fbee7f`, cabeça da PR #140, que é empilhada sobre #139. Nova branch: `agent/native-critical-euler-balance`. Nenhuma PR anterior foi alterada ou mesclada automaticamente.

São reutilizados:

- #140: `CarryMovingSigma.moving_schur_curvature_expanded`, para o pivô móvel da sequência canônica, em qualquer setor, com inversibilidade do prefixo central;
- #41: a relação de Schur sem sinal e `NativeMomentOrthogonalization.native_inverseSchur_boundary_energy`, com a energia original de bordo e o fator quatro;
- #43: `CarryCriticalMixed.source_nonlinear_margin_pos` e `source_correction_numerator_pos`, obtidos das caixas integrais theta da fonte original, para a regressão finita de sinal;
- as definições originais dos momentos, acoplamentos, fonte de bordo, entradas de paridade e característica completada.

A operação `jetEuler v i = i*v i` é uma operação nas coordenadas de ordem de jet, após a síntese completada que determina os momentos. Não foi identificada com profundidade radial, profundidade de carry, frequência material ou outro gerador físico. Não se mudou a sequência, a câmera, a métrica ou a amplitude.

## B — Identidade nova: separar os termos que já são ortogonais

Seja d≥1 a ordem do polinômio crítico, com prefixo de tamanho d, e

\[
 v=(-A^{-1}b,1),\quad p=\operatorname{Schur}_{s,d},\quad a=v_{d-1},
 \qquad R_i=(i-d)v_i\quad(0\le i<d).
\]

O residual R é de grau estritamente menor. Ele é derivado do mesmo vetor v; não substitui o estado ou a fonte original. Defina as formas originais

\[
 B=Q_{s+1,d+1}(v),\qquad R_* = Q_{s+1,d}(R),
\]

onde Q é `sourceMomentQuadratic` da sequência original. A soma ponderada da #140 é

\[
 W=\sum_{i,j=0}^d v_iv_j(i+j+s+1)(2(i+j+s)+3)h_{i+j+s+1}.
\]

`stationary_weighted_reduction` e `canonical_weighted_reduction` provam exatamente:

\[
 \boxed{W=(2d+s+1)(4d+2s+3)B-(16d+8s+6)a p+4R_*.}
\]

A prova não pressupõe positividade. Primeiro mantém separadamente os dois pareamentos mistos de Euler; depois usa a simetria da forma e a relação original `H v = snoc 0 p`. `stationary_shift_pair` mostra que os termos contra um vetor de grau menor são determinados por seu coeficiente superior e pelo próprio p. Nenhum cruzamento é descartado por estimativa.

`canonical_curvature_balance` transporta a identidade ao pivô móvel, usando p''(0)=-2W. Ela vale em todos os setores naturais, sob a inversibilidade central do prefixo. A fórmula inclui explicitamente s nos índices e nos pesos.

`stationary_weighted_lower` usa, separadamente, a hipótese de positividade semidefinida do **prefixo deslocado antigo** para deduzir R_*≥0. Essa hipótese não decorre de inversibilidade e está explícita. Assim, `canonical_curvature_negative_of_source_budget` fornece o critério suficiente:

\[
 (16d+8s+6)a p < (2d+s+1)(4d+2s+3)B
 \quad\Longrightarrow\quad p''(0)<0,
\]

quando o prefixo deslocado antigo é semidefinido positivo. O critério mantém uma comparação concreta entre formas originais; sua hipótese não foi demonstrada em toda ordem. A identidade completa continua válida mesmo quando o critério suficiente falha.

## C — Transporte ao bordo físico e sinal finito da fonte original

`NativeBoundaryBalance.lean` define `nativeSectorEnergy` usando literalmente `nativeSourceFiniteBoundaryEnergy` e `nativeSourceBoundaryFromParity`. `native_sector_energy_eq` preserva a calibração E=4Q da PR #41. Não se interpreta essa energia assinada como uma norma positiva sem prova de seu sinal.

O setor deslocado s+1 é realizado por `nativeNextEnergy`: para s=0, é o setor ímpar original; para s=1, é o setor par original com a primeira coordenada zero. `source_quadratic_shift_two` prova esse deslocamento de endereço por preenchimento com zero. Não há reescala de fonte ou métrica.

`native_weighted_balance` fornece, nos dois setores físicos,

\[
 4W=(2d+s+1)(4d+2s+3)E_{\mathrm{next}}(v)
 -(16d+8s+6)a E_s(v)+4E_{\mathrm{next}}(R).
\]

São as energias completas de bordo limite, com todos os cruzamentos. Não se afirma aqui um sinal em cada profundidade radial, nem uma cota nova para as caudas em todos os setores. As passagens radiais precisam conservar seus erros: a identidade de bordo não elimina essa obrigação. As cotas históricas da #139 continuam disponíveis nos casos já provados.

### Segunda direção par: sinal realmente certificado

`SourceSignRegression.lean` reutiliza as duas desigualdades integrais da #43. Delas, junto da positividade inicial já provada na fonte, deduz:

\[
 3h_1^3-20h_0h_1h_2+21h_0^2h_3>0.
\]

Para a direção original v=(-h1/h0,1), `second_even_weighted_positive` prova

\[
 W=\frac{3h_1^3-20h_0h_1h_2+21h_0^2h_3}{h_0^2}>0.
\]

Finalmente, `second_even_sigma_curvature_negative` prova p''(0)<0 para `sigmaSchur · 0 1`, sem hipótese externa. Trata-se de curvatura **sigma do pivô móvel**; não é a correção radial da #43, embora aproveite uma desigualdade da mesma fonte. Não se usou positividade de H6/K6, zeros ou alturas como premissa. É uma regressão finita rigorosa, não uma lei all-order nem uma prova exclusivamente geométrica sem certificação theta.

## D — Controle que impede uma inferência indevida de sinal

`SignControl.lean` é um teste sintético de álgebra, sem substituir a fonte Carry. A sequência do controle começa por (1,1,2,1) e tem todas as entradas estritamente positivas. Foram provados exatamente:

- prefixos antigos não deslocado e deslocado de tamanho um positivos definidos;
- bloco não deslocado de tamanho dois positivo definido, com pivô igual a 1;
- vetor crítico exatamente (-1,1);
- balanço deslocado B=-2 e soma ponderada W=-16;
- quatro equações da recorrência logarítmica com coeficientes racionais iniciais (1,-1,0,-1/3,1/3).

Isso demonstra que esses dados algébricos e sinais finitos não implicam W>0. O controle não satisfaz a fonte completada original e não a refuta; identifica precisamente a necessidade de informação adicional daquela fonte. Também não foi formalizada aqui uma realização analítica infinita do controle: a recorrência foi conferida somente nos quatro índices indicados.

## E — Validação e menor obrigação restante

`validate.sh` compilou os seis módulos matemáticos novos e `Audit.lean`, com avisos como erros. Passaram `lake build --wfail` (8.849 tarefas), as auditorias Foundation/Geometry/Analysis e a busca de escapes proibidos. Os logs extensos de Analysis e do build raiz estão compactados em `evidence/`.

A auditoria transitiva tem dois níveis para os resultados da fonte: a identidade geral bloqueia o uso das desigualdades finitas da #43; a regressão finita exige essas desigualdades como proveniência. Ambas bloqueiam os certificados posteriores de positividade do sexto pivô. O controle sintético tem raízes auditadas separadamente. `#print axioms` conferiu 38 declarações novas. A auditoria geral percorreu 58.113 dependências de três raízes; a regressão da fonte, 58.954 dependências de uma raiz; o controle, 15.953 dependências de cinco raízes. Foram permitidos somente `propext`, `Classical.choice` e `Quot.sound`.

São reutilizados Mathlib e objetos históricos da cadeia #140/#139. O manifesto conferiu 367 objetos de pesquisa, incluindo os módulos em subpastas, sem divergências. O ambiente local do operador conserva a investigação theta16 em andamento; nenhum arquivo dela foi editado ou adotado como uma nova dependência validada. Esta não é uma reconstrução histórica limpa.

Reprodução no host `llm`:

```bash
bash research/native-critical-euler-balance/validate.sh
python3 research/native-critical-euler-balance/cache_manifest.py
```

O próximo teorema de sinal deve controlar o balanço deslocado B da **mesma direção crítica**, em comparação com a p e o residual antigo, a partir da fonte original. A forma antiga deslocada pode controlar R_* quando seu certificado estiver disponível. O termo B não pode ser declarado positivo somente porque existem normas positivas nos canais.

A orientação de curvatura, mesmo que obtida em todas as ordens, não provaria isoladamente positividade dos valores centrais dos pivôs. A obrigação all-order da sequência canônica permanece. A contribuição atual é o cancelamento exato que reduz a soma ponderada a um balanço explícito de energias da fonte, acompanhado de um sinal finito genuinamente certificado e de um controle que refuta a inferência genérica insuficiente.
