# Terceira direção C3: prefixos a partir da fonte

**Resultado: PARTIAL.** O Lean descarrega a invertibilidade do prefixo antigo da terceira direção par diretamente das quatro caixas C3 preexistentes. No setor ímpar, certifica uma entrada positiva do prefixo a partir das mesmas caixas e prova que esses quatro coeficientes, considerados apenas como dados algébricos, não determinam sua invertibilidade. Não se prova nova margem da cabeça nem o sinal da terceira direção pela fonte C3; o sinal finito com caixas theta da PR #144 permanece válido, com aquela proveniência.

## Fonte e resultados

Base `1e71b90a9d503254310c41ebeb60528247cea6bd`, PR #146 empilhada na #145. O arquivo `ThirdSourcePrefix.lean` reutiliza `canonical_two_even_determinant_pos_from_c3` da #69 e a ponte da #70. Essa positividade pertence ao **prefixo antigo** 2×2, já certificado por caixas derivadas da fonte original; não é o sinal do novo pivô da terceira direção.

`third_even_prefix_isUnit_from_c3` prova incondicionalmente `IsUnit (sourceMomentMatrix nativeH 0 2)`. `third_even_gate_no_prefix_assumption` aplica o resultado ao gate da #145 e obtém

\[
 p_{0,2}>0 \quad\Longleftrightarrow\quad
 c_5<\frac{E_0}{5c_0},
\qquad E_0=-3c_1c_4-c_2c_3-b^TA^{-1}b.
\]

O termo de Schur mantém todos os cruzamentos do prefixo. A equivalência identifica uma obrigação; **não** demonstra a desigualdade nem o sinal do novo pivô. Para a rota C3 direta ainda faltam caixas suficientemente estreitas de `c₄,c₅` e da cabeça/cauda original.

## Setor ímpar e controle de insuficiência

`third_odd_prefix_first_entry_pos_from_c3` usa as mesmas quatro caixas para provar `c₁²−2c₀c₂>0`, a primeira entrada do prefixo Bézout ímpar. `odd_prefix_det_shift` prova que alterar algebricamente somente `c₄` por `d` muda o determinante do prefixo por

\[
\det A_{\rm odd}(c+de_4)=\det A_{\rm odd}(c)
 -4c_0(c_1^2-2c_0c_2)d.
\]

Também isolamos a desigualdade concreta que resolveria a invertibilidade ímpar. Definindo

\[
a=c_1^2-2c_0c_2,\quad b=c_1c_2-3c_0c_3,\quad
L_4=\frac{a(2c_2^2-2c_1c_3)-b^2}{4c_0a},
\]

`odd_prefix_det_pos_iff_c4` prova, para `c₀>0` e `a>0`, que o determinante do prefixo ímpar é positivo se e somente se `c₄<L₄`. Ambas as condições laterais já estão descarregadas das caixas C3 originais. `third_odd_prefix_isUnit_of_c4_source_bound` demonstra que essa desigualdade de fonte é suficiente para a invertibilidade do prefixo de momentos, e `third_odd_gate_of_c4_source_bound` a usa para liberar a equivalência da #145 envolvendo `c₆`. A desigualdade `c₄<L₄` permanece hipótese: não se usa a aproximação numérica como certificado.

`third_odd_prefix_four_coefficients_insufficient` usa `c₀>0` e a entrada positiva para construir uma sequência de controle com os mesmos `c₀,…,c₃` da fonte e determinante ímpar nulo. É um contraexemplo **à suficiência dessas informações algébricas isoladas**; não é outra fonte física Carry nem prova que o prefixo físico seja singular. Relações adicionais da fonte podem excluir a perturbação. A rota C3 ímpar precisa de informação adicional, começando por `c₄`, para controlar o prefixo; para a terceira margem completa a #145 identifica a dependência até `c₆`.

## Auditoria e continuidade

`ThirdSourcePrefixAudit.lean` audita oito raízes novas junto das raízes originais da #145, exige as caixas C3 e a recorrência/transporte Schur e bloqueia os consumidores theta/de sinal nomeados. A auditoria dos tipos e corpos não demonstra ausência semântica de toda equivalência possível. `#print axioms` mostra somente `propext`, `Classical.choice` e `Quot.sound`.

```bash
bash research/c3-tilt-prime/validate_third_source_prefix.sh
```

O build geral e as auditorias de Foundation/Geometry/Analysis são executados separadamente na integração com `main`. Dependências anteriores são reutilizadas dos caches já construídos. Nenhum arquivo histórico, fonte, pin ou métrica foi modificado.

Próximo passo matemático mínimo: construir caixas verificadas da **cabeça C3 original e cauda**, incluindo Gamma/chart, para os jets até ordem 10 e 12, e confrontar respectivamente `c₅` e `c₆` com os limiares completos da #145. A generalização all-order exige uma propriedade de margem por ordem e setor; não decorre do prefixo par ou da positividade finita já conhecida.
