# Resto transversal e primeiras falhas certificadas

Use \(d=\sigma-\tfrac12\), a família nativa de jatos do logaritmo do
módulo completado, e a matriz confluente intercalada \(C_N(d)\)
com blocos de paridade \(H_{\lceil N/2\rceil}(d)\) e
\(K_{\lfloor N/2\rfloor}(d)\). A investigação mede a primeira dimensão
com direção negativa e a permanência de positividade em intervalos
inteiros. Os dados vêm dos coeficientes da característica da fonte.

## Resto explícito de ordem arbitrária

O módulo [SigmaTransverseAllOrder](../native-moving-schur-sigma/SigmaTransverseAllOrder.lean)
dá o Taylor transversal da família nativa. Para o termo de índice \(j\),
\[
h_j(d)=\sum_{r\ge0}(-1)^r
 \binom{2j+2r+1}{2r}h_{j+r}(0)d^{2r}.
\]
O [majorante do CSA](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/main/CarrySelfAdjointOperator/CompletedNativeLogCoefficientMajorant.lean)
dá \(|h_k(0)|\le q^{k+1}\), com \(q=22/175\), sem hipótese de sinal.
A série ímpar \(R(z)=\sum_j h_j(0)z^{2j+1}\) converge no disco
\(|z|<1/\sqrt q\). No germe central ela coincide com \(-F'(z)/(2F(z))\).
A identidade \(F'+2RF=0\) se prolonga pelo teorema da identidade no
disco dentro da faixa de analiticidade da fonte. Como \(F(0)\ne0\),
a solução da equação não se anula nessa componente. Isso identifica
a média das duas translações imaginárias de \(R\) com o jato nativo
nos deslocamentos usados aqui, todos com \(|d|<1/2\).

Para \(L\ge1\), escreva \(E_{j,L}(d)\) para a cauda que começa em
\(d^{2L}\). Temos
\[
|E_{j,L}(d)|\le
\frac{q^{j+L+1}\binom{2j+2L+1}{2L}|d|^{2L}}
 {(1-\tfrac38|d|)^{2j+2L+2}}.
\]
Com \(a=2j+1\) e \(k\ge 2L\), a identidade do produto de binômios dá
\(\binom{a+k}{k}\binom{k}{2L}
=\binom{a+2L}{2L}\binom{a+k}{k-2L}\).
Usamos \(\binom{k}{2L}\ge1\), majoramos a soma nos índices pares
pela soma de todos os índices e aplicamos a série binomial negativa
em \(\sqrt q|d|\le 3|d|/8\). Assim, \(L=2\) controla diretamente
o resto de quarta ordem, e \(L>2\) preserva os cancelamentos nas
formas quadráticas dos coeficientes finitos antes de cobrar a cauda absoluta.

## Direção fixa e complemento de Schur

Num setor, escreva \(M(d)\) para o bloco ampliado e \(A(d)\) para o
prefixo. Use o vetor crítico central \(p=(-A(0)^{-1}b(0),1)\) e
\(u(d)=(M(d)p)_{\mathrm{antigo}}\). Sempre que \(A(d)\) é invertível,
a mudança triangular de coordenadas dá
\[
\sigma(d)=p^\top M(d)p-u(d)^\top A(d)^{-1}u(d).
\]
Como \(u(0)=0\) e a família é par, \(u(d)=O(d^2)\). Quando \(A(d)\succ0\),
o termo subtraído é não negativo. A negatividade de \(p^\top M(d)p\)
já dá uma direção negativa mesmo sem hipótese sobre \(A(d)\).

Escrevendo \(M(d)=M(0)-d^2M_1+d^4M_2+O(d^6)\), obtemos o termo
de quarta ordem do pivô móvel
\[
[d^4]\sigma(d)=p^\top M_2 p
 - \bigl((M_1p)_{\mathrm{antigo}}\bigr)^\top A(0)^{-1}
   (M_1p)_{\mathrm{antigo}} .
\]
No teste suficiente basta avaliar a forma fixa
\(\sigma_0-Td^2+R(d)\). Em \(d=\sqrt{2\sigma_0/T}\), com
\(\sigma_0,T>0\), o caso \(|R(d)|<\sigma_0\) certifica uma direção
negativa. Para estimar \(|R(d)|\), o verificador calcula cada forma
quadrática dos coeficientes de ordem \(2,\ldots,L-1\) antes de tomar
o módulo, e só usa a cota entrada a entrada na cauda infinita.

O teste passou nas duas paridades para os graus 3, 4, 5, 8 e 12. No
grau 5 par, por exemplo, \(\sqrt{\sigma_0/T}\) está perto de
\(0{,}005757856\) e a cota para \(|R|/\sigma_0\) é inferior a
\(0{,}000233\) no ponto de teste \(\sqrt{2\sigma_0/T}\).

## Positividade em faixas inteiras

Se \(P\) tem como colunas os vetores centrais ortogonais divididos
pelas raízes de seus pivôs, então \(P^\top M(0)P=I\).
Para \(|d|\le\delta\), o programa transforma cada coeficiente finito
por \(P\), soma seus módulos entrada a entrada com pesos
\(\delta^{2r}\) e soma a cota de cauda transformada com \(|P|\).
A maior soma de linha controla a norma do erro simétrico
\(P^\top(M(d)-M(0))P\). Uma cota estritamente menor que um garante
positividade em toda a faixa, inclusive entre os pontos testados.

| Raio \(\delta\) | Prefixo positivo para todo \(|d|\le\delta\) | Cota de norma menor que | Primeira falha em \(|d|=\delta\) |
|---:|---:|---:|---:|
| \(10^{-2}\) | 10 | 0,449 | 11 |
| \(10^{-6}\) | 17 | 0,267 | 18 |
| \(10^{-12}\) | 26 | 0,656 | 27 |

Também foram certificados os pontos \(0{,}2\), \(0{,}1\), \(0{,}05\),
\(0{,}02\), \(10^{-3}\), \(10^{-4}\), \(10^{-8}\) e \(10^{-10}\), com
primeiras dimensões \(8,9,9,10,13,15,21,24\), respectivamente.
Em cada ponto todo pivô precedente é estritamente positivo nos
intervalos, permitindo identificar a primeira dimensão. A simetria
nativa dá os mesmos resultados do outro lado.

## Reproduzir e conferir a fonte

`certify-transverse-schur.py` usa Arb, por Python-FLINT 0.8.0,
com 1024 bits e \(L=32\). O programa obtém as caixas de momentos
do logaritmo derivado da característica
\(\xi(s)=s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s)/2\).
A igualdade com a função nativa na faixa é
`completedNativeOperatorCharacteristic_eq_completedRiemannZeta`,
com a forma polar removida em
[CompletedNativeEntireComparison, CSA #120](https://github.com/thiagomassensini/carry-self-adjoint-operator/pull/120).
A convenção \((-1)^j/2\) extrai do coeficiente de ordem \(2j+1\)
da derivada logarítmica em \(s\) o momento de altura pretendido.
O programa verifica os pontos deslocados tanto pela série central
mais sua cauda certificada quanto por Taylor direto no ponto
\(s=\tfrac12+d\) e exige acordo das caixas e da primeira dimensão.

Na VM, na raiz do GoN:

```bash
/home/thlinux/miniforge3/bin/python3 research/projective-chiral-complex-cauchy/certify-transverse-schur.py
```

Os resultados finitos usam intervalos rigorosos do Arb e a cota
analítica derivada acima. A nova cota e os testes de intervalos
permanecem fora da formalização Lean. A extensão a toda ordem exige uma cota que
acompanhe os prefixos e suas margens centrais.
