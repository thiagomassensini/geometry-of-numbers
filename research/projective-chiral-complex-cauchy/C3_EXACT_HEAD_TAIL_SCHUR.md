# Cabeça e cauda C3 exatas na direção de Schur

A investigação usa a cabeça acelerada C3/64 da PR #69, com a
semente e o bordo originais, e a congruência de Bézout da PR #70.
O objetivo é avaliar cada cruzamento na própria direção crítica,
antes de calcular o orçamento total da cauda.

## Resultados recuperados das provas Lean

- `native_c3_head_tail` recompõe o bracket C3 completo com o mesmo
  termo de bordo somado à cabeça e subtraído da cauda.
  `native_c3_tail_acceleration` identifica separadamente o resto
  como a soma de diferenças de ordem 14. [Fonte C3](../c3-fourteenth-tail/InfiniteC3Tail.lean)
- `sourceSchur_eq_scaled` dá \(p_B=c_0^2p_H\), com a mesma
  direção crítica transportada por uma matriz triangular dos
  coeficientes. `native_residual_four_terms_boundary_repartition`
  mantém \(HH+HT+TH+TT\) e permite redistribuir o mesmo bordo.
  `sourceSchur_lastCoefficient_update` isola a ação do último
  coeficiente em uma única diagonal. [Congruência](../tfvd-bezout-schur-residual/SourceSchur.lean)
  · [Lei de fronteira](../tfvd-bezout-order-compensation/TfvdBoundaryLaw.lean)
  · [Atualização do pivô](../tfvd-bezout-order-compensation/SchurThreshold.lean)
- Para o corte de células do C2, `accelerated_critical_error` melhora
  o orçamento da mesma direção de \(C_{\rm crit}/[4(4M-1)]\) para
  \(5C_{\rm crit}/[4(4M-1)^3]\). O denominador \(F\) permanece
  completo na observação acelerada. `accelerated_green_tail_ledger`
  demonstra a identidade dos quatro termos para a forma Green.
  [Cota cúbica](../tfvd-infinite-fourth-tail/AcceleratedCritical.lean)
  · [Identidade polarizada](../tfvd-infinite-fourth-tail/AcceleratedGreen.lean)

## Avaliação direta dos quatro termos

Para \(M=64\), seja \(a=3M+2\). O verificador usa o prefixo
literal \(1+\sum_{k<M}\Delta^2 f_s(3k+2)\), \(f_s(x)=x^{-s}\),
e o mesmo bordo \(Bf_s(a)\). A cauda original antes de subtrair
o bordo tem a avaliação
\[
3^{-s}\left(
\zeta(s,a/3)-2\zeta(s,(a+1)/3)+\zeta(s,(a+2)/3)
\right).
\]
Para \(\Re s>1\), a identidade segue da soma das três pernas nas
progressões originais. O polo comum das funções de Hurwitz se
cancela. A convergência normal do segundo incremento estende a
identidade ao germe central. O verificador usa as funções de
Hurwitz deflacionadas e completa cada parcela com o mesmo
fator \(\Xi(s)/(1-3^{1-s})\).

Depois da síntese, extraímos os coeficientes pares em altura de
cada parcela. Seja \(c=c^H+c^T\) e \(L(c)_{ij}=c_{i-j}\) para
\(i\ge j\). Para o vetor de Schur mônico \(p\) dos momentos
completados, usamos \(z=L(c)^{-\top}c_0p\). A congruência dá
\[
c_0^2\sigma_{s,n}
= z^\top B_s(c)z
=HH+HT+TH+TT.
\]
Para construir \(p\) basta resolver o bloco antigo. No teste
de dominância, a desigualdade \(HH>|HT|+|TH|+|TT|\) é verificada
em intervalos antes de concluir o sinal estrito do pivô novo.
Cada termo é somado com sinal sobre todas as coordenadas antes
de tomar o módulo. A avaliação de \(\sigma_{s,n}\) pela
fórmula de Schur confere a recomposição.

| Setor | Grau | \(HH\) aproximado | \(\sum HH,HT,TH,TT\) aproximada |
|---|---:|---:|---:|
| par | 2 | \(2{,}75460\cdot10^{-14}\) | \(2{,}75460\cdot10^{-14}\) |
| ímpar | 2 | \(1{,}99724\cdot10^{-17}\) | \(1{,}99724\cdot10^{-17}\) |
| par | 56 | \(3{,}33035\cdot10^{-195}\) | \(1{,}34219\cdot10^{-463}\) |
| ímpar | 56 | \(7{,}01521\cdot10^{-197}\) | \(3{,}26800\cdot10^{-468}\) |

A cabeça supera a soma dos módulos dos três termos de cauda nos
quatro casos. No setor ímpar de grau 56, a diferença relativa a
\(HH\) está encerrada perto de \(4{,}65845\cdot10^{-272}\).
Nesse caso os três termos de cauda são individualmente
negativos. O sinal do resíduo depende de preservar esse
cancelamento até mais de 270 casas em escala relativa.

O teste da última diagonal mantém todos os coeficientes anteriores
exatos, inclusive \(c_0\). Se \(m=2n+s+1\), a contribuição isolada
da cauda \(c^T_m\) para \(p_B\) é \(-m c_0c^T_m\). No setor ímpar
de grau 56, essa correção é cerca de
\(-4{,}04738\cdot10^{271}\) vezes \(p_B\). Mesmo nessa perturbação
de posto um, a precisão da cauda da última diagonal é decisiva.

A separação também tem um efeito analítico verificável. No
primeiro zero não real do fator de câmera,
\(s_\star=1+2\pi i/\log 3\), o módulo da cabeça antes do
completamento está encerrado perto de \(7{,}38295\cdot10^{-24}\),
estritamente longe de zero. Como \(1-3^{1-s}\) tem zero simples
e \(\Xi(s_\star)\ne0\), a cabeça completada tem ali um polo
simples. A cauda completada tem o polo oposto, pois a soma é
a característica regular. Isso localiza uma fonte concreta
de cancelamento entre os coeficientes das duas parcelas.

## Janela transversal pela mesma recomposição

A \(d=10^{-100}\), a avaliação da característica por cabeça e
cauda C3 dá a primeira falha na dimensão intercalada 114 e na
ordem 58 do bloco não deslocado. O pivô na dimensão intercalada
114 está encerrado perto de \(-1{,}69770150155\cdot10^{-467}\).
A dimensão 113 permanece positiva em toda a faixa \(|d|\le10^{-100}\). A verificação reaproveita a [cota relativa transversal](TRANSVERSE_RELATIVE_WINDOW.md)
com os momentos do centro vindos da composição C3.

O verificador fornece certificados finitos de Arb com as identidades
Lean precedentes como base matemática. A avaliação por intervalos
dos quatro cruzamentos e a representação Hurwitz desta rotina
permanecem fora da formalização Lean. Uma desigualdade de dominância
em ordem arbitrária ainda exige uma estimativa da margem depois
dos cancelamentos.

```bash
/home/thlinux/miniforge3/bin/python3 research/projective-chiral-complex-cauchy/certify-c3-head-tail.py
```
