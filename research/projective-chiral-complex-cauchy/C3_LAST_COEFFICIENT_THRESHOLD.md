# Limiar de Schur com duas avaliações da fonte completada

Esta rodada testa o limiar da [PR #316](https://github.com/thiagomassensini/geometry-of-numbers/pull/316)
nos graus 56 e 57, nos setores par e deslocado. Escrevemos
\(C(u)=\sum_j c_j u^j\), com \(u=z^2\) no centro, e
\(h(u)=-C'(u)/C(u)\). Para setor \(s\in\{0,1\}\) e grau \(n\)
o coeficiente novo é \(c_m\), onde \(m=2n+s+1\).

## Limiar calculado antes de admitir o último coeficiente

Pela recorrência da fonte,
\[
c_0 h_j=-(j+1)c_{j+1}-\sum_{k<j}c_{j-k}h_k.
\]
Logo \(c_0,\dots,c_{m-1}\) determinam \(h_0,\dots,h_{m-2}\).
O prefixo \(A_s\) da Hankel e a coluna \(b_s\) de acoplamento
só usam esses índices. Definimos
\[
T_{s,n}=-\frac{c_0\,b_s^\top A_s^{-1} b_s+
               \sum_{k=0}^{m-2} c_{m-1-k}h_k}{m},
\qquad
\sigma_{s,n}=\frac{m}{c_0}(T_{s,n}-c_m).
\]
Essa é a forma Hankel do
[limiar Lean de Bézout](../tfvd-bezout-order-compensation/SchurThreshold.lean),
cujo pivô é \(c_0^2\sigma_{s,n}\).
O verificador usa zero no canto novo para ler
\(-b_s^\top A_s^{-1}b_s\), mantendo toda a coluna de cruzamentos.
A reconstrução do limiar recebe exatamente \(m\) coeficientes.

O prefixo vem dos jatos da característica completada direta.
Para obter a caixa de \(c_m\), o programa usa o [bracket C3](C3_EXACT_HEAD_TAIL_SCHUR.md)
com o prefixo finito, a semente e a cauda inteira das três
progressões por Hurwitz. O mesmo termo de bordo entra com sinais
opostos, de modo que o programa o cancela algebricamente antes de
dividir pela carta de câmera. O fator de completamento e a convenção
de altura são os mesmos nas duas avaliações.

O certificado exige \(\inf[T_{s,n}]>\sup[c_m]\). Todos os pivôs
antigos até o grau 56 foram verificados nos dois setores.
As linhas abaixo mostram centros arredondados dos intervalos de Arb.

| Setor | Grau | \(m\) | \(T_{s,n}-c_m\) | \((T_{s,n}-c_m)/|c_m|\) | \(\sigma_{s,n}\) |
|---|---:|---:|---:|---:|---:|
| par | 56 | 113 | \(2{,}38931\,10^{-465}\) | \(1{,}03077\,10^{-46}\) | \(5{,}43112\,10^{-463}\) |
| deslocado | 56 | 114 | \(5{,}76655\,10^{-470}\) | \(5{,}17145\,10^{-47}\) | \(1{,}32239\,10^{-467}\) |
| par | 57 | 115 | \(1{,}23337\,10^{-474}\) | \(2{,}33026\,10^{-47}\) | \(2{,}85319\,10^{-472}\) |
| deslocado | 57 | 116 | \(2{,}50740\,10^{-479}\) | \(1{,}01136\,10^{-47}\) | \(5{,}85086\,10^{-477}\) |

Os certificados dão positividade definida central para o bloco
intercalado de dimensão 116. A folga relativa piora por um fator
de aproximadamente 4,4 no setor par e 5,1 no deslocado entre os
graus 56 e 57.

## Efeito exato de mudar os dois últimos coeficientes

Para \(n\ge1\), escreva \(p=(-A_s^{-1}b_s,1)\) para o vetor
mônico e \(\sigma_{\rm ant}=\sigma_{s,n-1}>0\). Mantendo os
coeficientes até \(c_{m-2}\) fixos, uma alteração \(\delta\) em
\(c_{m-1}\) deixa \(A_s\) fixo e altera só a última entrada
de \(b_s\), em \(-(m-1)\delta/c_0\). Na convolução do limiar,
os dois termos afetados são \(c_{m-1}h_0\) e \(c_1 h_{m-2}\).
Usando \(h_0=-c_1/c_0\) e
\((A_s^{-1})_{n-1,n-1}=1/\sigma_{\rm ant}\), segue
\[
T_{s,n}(\delta)=T_{s,n}(0)+a\delta-\beta\delta^2,
\quad
a=\frac{c_1}{c_0}-\frac{2(m-1)}m p_{n-1},
\quad
\beta=\frac{(m-1)^2}{m c_0\sigma_{\rm ant}}.
\]
A fórmula é exata. Para erros independentes
\(|\delta|\le r\) em \(c_{m-1}\) e \(|e|\le t\) em \(c_m\),
o mínimo da folga é
\[
g-|a|r-\beta r^2-t,\qquad g=T_{s,n}(0)-c_m.
\]
Ela segue da concavidade em \(\delta\) e do coeficiente
\(-1\) de \(e\). Para \(t=0\), o verificador escolhe um raio
conservador abaixo de
\(g/[2(|a|+\sqrt{\beta g})]\) e confere a lei quadrática nos
dois extremos por recomputação da recorrência. No grau 57
deslocado, a tolerância relativa isolada certificada para
\(c_{115}\) é maior que \(1{,}81\,10^{-50}\).

## Orçamento simultâneo para o prefixo inteiro

O teste conjunto parte do bloco de grau 57 deslocado certificado
acima. Considere erros independentes
\(|\delta c_j|\le\epsilon |c_j|\) para \(j<m\), com \(c_m\)
fixo nesta primeira etapa. Ponha \(U=\delta C/C\). A identidade
da derivada logarítmica dá exatamente
\[
\Delta h=-\frac{U'}{1+U}.
\]
Para limitar seus coeficientes, construímos o majorante formal
\[
D=\epsilon
\left(\sum_{j<m}|c_j|u^j\right)
\left(\sum_{k\le m}|[u^k]C^{-1}|u^k\right).
\]
Com \(D(0)<1\), a série geométrica de \(1/(1+U)\) mostra que
\(|[\Delta h]_j|\le [u^j]D'/(1-D)\). As operações só exigem os
coeficientes até \(c_m\). Seja \(P\) a base central normalizada,
com \(P^\top H_sP=I\). Com \(E\) a matriz Hankel do majorante,
\(\max_i\sum_j (|P|^\top E|P|)_{ij}\) limita a norma do erro
conjugado. Uma cota abaixo de 1 certifica o bloco inteiro em
todas as caixas, inclusive combinações de erros simultâneos.

A rotina certifica \(\epsilon>5{,}96\,10^{-219}\) e erro
normalizado menor que \(0{,}251\) no grau 57 deslocado. Essa
é uma tolerância suficiente para este bloco. A certificação do
limiar acima usa as caixas individuais da avaliação da fonte.

Pode-se também mover \(c_m\) depois do prefixo. Se
\(|\delta c_m|\le t\), só a última diagonal do Hankel varia,
por \(-m\delta c_m/\widetilde c_0\), onde \(\widetilde c_0\)
é o coeficiente após a variação do prefixo. Na base \(P\),
o acréscimo de norma é limitado por
\(t/[(1-\epsilon)g]\), usando a margem original
\(g=c_0\sigma_{s,n}/m\). Portanto
\[
\eta+\frac{t}{(1-\epsilon)g}<1
\]
é suficiente para as duas perturbações juntas quando
\(\eta\) limita o erro do prefixo. No grau 57 deslocado,
\(t=1{,}25\,10^{-479}\) cabe no orçamento junto com
\(\epsilon=5{,}96\,10^{-219}\).

## Reprodução e alcance

```bash
/home/thlinux/miniforge3/bin/python3 research/projective-chiral-complex-cauchy/certify-c3-last-coefficient.py
```

Os intervalos do cálculo usam Arb com 6144 bits. A equivalência
do limiar vem do Lean. As novas verificações são finitas e a lei
do penúltimo coeficiente está demonstrada algebricamente acima.
Uma cota inferior da folga válida à medida que a ordem cresce
continua em aberto.
