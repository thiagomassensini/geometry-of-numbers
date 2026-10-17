# Carry — quarto pivô material e obrigação theta de ordem 18

## Conclusão

**O sinal `p₃ > 0` ainda não foi demonstrado.** Esta rodada formaliza o
quarto passo bilinear, sua direção crítica e a equivalência exata entre o
sinal desse pivô e uma desigualdade da integral theta original.

O novo resultado não é um certificado de positividade. Ele identifica o
contraste analítico da fonte que precisa ser estimado, mantendo os canais
anteriores, os cruzamentos ordenados, a normalização e a cauda inteira.

Este `p₃` é o quarto pivô do **bloco residual par** e corresponde ao quinto
pivô do Hankel não deslocado, depois de restaurar o centro. Não é o pivô
histórico da oitava fonte no setor ímpar.

## Base e proveniência

- Repositório alterado: `thiagomassensini/geometry-of-numbers`.
- Base: `c1acf41d0d842861e85ceb50e0a79fd833b530f3`, merge do PR #20.
- Operador consultado sem alterações:
  `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- `momentos`, sem alterações: `a54f267365d5d8c965376734b17b10ae89ed3f74`.
- Mesmos pins de Lean, Mathlib e GreenFrame; nenhuma fonte, métrica ou
  normalização modificada.

Usamos literalmente os observáveis materiais já sintetizados:

$$
K(i,j)=\operatorname{carryMaterialResidualJet}(2(i+1),2(j+1))
=h_{i+j+2}-\frac{h_{i+1}h_{j+1}}{h_0}.
$$

Os `h_n` são os momentos da característica completada original. A igualdade
é o crosswalk demonstrado nos PRs #19 e #20, não a definição de outro estado.
Os índices são ordens confluentes de Taylor, não profundidade ou câmera.

## Quarto passo, com todos os cruzamentos

Mantemos a recorrência do PR #20:

$$
R_0=K,\quad p_r=R_r(r,r),\quad
R_{r+1}(i,j)=R_r(i,j)-\frac{R_r(i,r)R_r(r,j)}{p_r},\quad
\ell_r(i)=R_r(i,r)/p_r.
$$

Os sinais dos três pivôs antigos já estão provados pela fonte theta:
`p₀ > 0`, `p₁ > 0`, `p₂ > 0`. O novo pivô continua sendo

$$
p_3=R_2(3,3)-\frac{R_2(3,2)R_2(2,3)}{p_2}.
$$

Para dois vetores independentes `x,y : Fin 4 → ℝ`, o Lean verifica:

$$
\sum_{i,j<4}K(i,j)x_i y_j
=\sum_{r<3}p_r\Bigl(\sum_{i<4}\ell_r(i)x_i\Bigr)
                    \Bigl(\sum_{j<4}\ell_r(j)y_j\Bigr)
+p_3x_3y_3.
$$

Não se pressupõe sinal para `p₃`. A costura mantém as dezesseis entradas
ordenadas do bloco e é aplicada somente depois da síntese material completa.

## Combinação crítica efetiva

Construímos por substituição triangular, a partir das colunas reais já
extraídas:

$$
x_3=1,\quad x_2=-\ell_2(3),\quad
x_1=-\ell_1(2)x_2-\ell_1(3),\quad
x_0=-\ell_0(1)x_1-\ell_0(2)x_2-\ell_0(3).
$$

O Lean prova `x != 0` e `sum_i ell_r(i)*x_i = 0` para `r=0,1,2`.
Para qualquer segundo vetor `y`, o pareamento completo é `p₃*y₃`.
Em particular, a energia crítica é **exatamente `p₃`**.

Essa combinação é um vetor de coeficientes dos observáveis originais. Não é
uma nova fonte física ou uma família definida para realizar um Gram desejado.
O teorema `material_fourth_block_posDef_iff` verifica:

$$
(K(i,j))_{i,j<4}\succ0\quad\Longleftrightarrow\quad p_3>0.
$$

A implicação inversa usa somente os três sinais antigos já certificados e
a fatoração do PR #20. A implicação direta usa a direção crítica não nula.

## Apenas um novo momento

Defina o acoplamento já extraído, sem impor simetria antes da síntese:

$$
Q=\frac{K(3,0)K(0,3)}{p_0}
+\frac{R_1(3,1)R_1(1,3)}{p_1}
+\frac{R_2(3,2)R_2(2,3)}{p_2}.
$$

Depois da identidade de simetria da fonte, cada parcela é um quadrado
dividido por um pivô positivo; logo `Q ≥ 0`. A igualdade nova é

$$
\boxed{p_3=h_8-T,\qquad T=\frac{h_4^2}{h_0}+Q.}
$$

No código local, `T` usa `carryMaterialTaylorShift 9 0`, a escala material e
os acoplamentos existentes. Não recebe campos livres `h₀,h₄` como se fossem
novos estados. A identificação com os momentos é demonstrada na comparação.

`T` usa momentos somente até `h₇`. Portanto, a única nova informação
diagonal é `h₈`; o teste não pode ser substituído pelo seu sinal isolado.

## Cota exata para a característica completada

Se `c_n` é `completedNativeRealEvenCharacteristicCoefficient n`, a recorrência
literal da fonte fornece:

$$
c_0p_3=-9c_9-\sum_{k<8}h_kc_{8-k}-c_0T.
$$

Com

$$
B=-\frac{\sum_{k<8}h_kc_{8-k}+c_0T}{9},
$$

e o sinal já provado `c₀ > 0`, o Lean verifica:

$$
\boxed{p_3>0\quad\Longleftrightarrow\quad c_9<B.}
$$

O limiar `B` contém somente dados anteriores a `c₉`. O fator 9 é imposto
pela recorrência original; nenhuma constante é ajustada.

## A primeira desigualdade analítica ainda aberta

Denote `A_j = completedNativeThetaTailMoment j`. A identidade theta da
característica, com o sinal alternado e o fatorial originais, dá:

$$
c_9=\frac{A_{18}-1224A_{16}}{4\,18!}.
$$

O fator `1224 = 4·18·17` é verificado no Lean. Consequentemente:

$$
\boxed{
p_3>0\quad\Longleftrightarrow\quad
\int_0^\infty(1224u^{16}-u^{18})\,\theta_{\rm tail}(u)\,du
>-4\,18!\,B.
}
$$

As duas parcelas são integráveis pelos teoremas já existentes. A identidade
da integral é formalizada, incluindo a cauda inteira. O peso muda de sinal
em `u = sqrt(1224)`; não se descarta a parte negativa por o kernel theta
ser positivo.

**Primeiro enunciado não provado:** a desigualdade estrita acima para a fonte
theta efetiva e o limiar `B` derivado dos seus acoplamentos.
Os certificados de integrais usados no PR #20 vão até a ordem 14. Esta rodada
não produz enclosures analíticos novos de ordens 16 e 18, nem o controle
conjunto do limiar necessário para concluir a desigualdade.

O no-go anterior das caixas de ordem 14 em `CompletedNativeThetaBoxEighthObstruction`
é sobre outro teste, no setor ímpar. Ele alerta para a precisão das estimativas,
mas **não é utilizado como no-go para este pivô par**. Nenhum novo
contramodelo com campos arbitrários foi construído.

## Diagnóstico numérico, separado da prova

`diagnostic.py` recompõe a cadeia original:

`theta integral preservada → característica completada → recorrência h → p₃`.

O cache usa a variável `log(x)`. A coordenada theta do Lean é `log(x)/2`,
por isso o índice par `k` exige a conversão literal `cached[k] / 4^k`.
Não se aplica nenhuma renormalização adicional. Todos os nove momentos
recompostos são comparados ao arquivo canônico preservado em `momentos`.

O replay usa 100 e 180 dígitos decimais e também calcula a energia da direção
crítica, que concorda com o pivô na precisão verificada:

$$
p_3\approx1.6662810117824798035962736\times10^{-26},
$$

$$
B-c_9\approx9.2038101473079750259048941\times10^{-28},
$$

$$
1224A_{16}-A_{18}+4\,18!B
\approx2.3570492831854851851956157\times10^{-11}.
$$

São diagnósticos de ponto flutuante baseados no cache, **não intervalos
certificados da integral nativa**. Nenhum valor desse replay entra em uma
prova Lean. Não há nova quadratura, tabela de zeros, ajuste de momentos ou
mudança do operador.

## Status e próximos passos

| Resultado | Status |
|---|---|
| Costura bilinear de quatro observáveis | PROVADO em Lean |
| Vetor crítico não nulo e cancelamento dos três canais antigos | PROVADO em Lean |
| Energia crítica exatamente igual a `p₃` | PROVADO em Lean |
| Positividade do bloco equivalente a `p₃ > 0` | PROVADO em Lean |
| Identidades de recorrência e equivalência com a integral theta | PROVADO em Lean |
| Fator real do bloco ampliado, dada a cota da fonte | CONDICIONAL, provado em Lean |
| Sinal positivo nos replays de 100 e 180 dígitos | TESTE NUMÉRICO |
| Desigualdade analítica da fonte e `p₃ > 0` | ABERTO |

O próximo passo natural é certificar esse contraste theta com erro menor
que sua margem e controlar o limiar antigo simultaneamente. Apenas aumentar
a precisão da matriz finita não demonstra a estimativa da integral.

O arquivo `validation.json` guarda os comandos e resultados; `new-roots.json`
e `footprints.json` registram os tipos públicos auditados; `provenance.json`
registra commits e hashes. Os logs Lean estão em `evidence/`. O replay
numérico tem registro próprio em `diagnostic.json`, separado dos certificados.
