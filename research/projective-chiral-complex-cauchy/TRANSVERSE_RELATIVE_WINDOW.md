# Orçamento relativo e primeira falha a \(10^{-100}\) do centro

Escrevemos \(d=\sigma-\tfrac12\). A dimensão intercalada \(N\) conta as
direções dos dois setores, de modo que \(C_N(d)\) contém
\(H_{\lceil N/2\rceil}(d)\) e \(K_{\lfloor N/2\rfloor}(d)\).
A ordem em `sigmaFirstFailureOrder` conta exclusivamente o bloco
não deslocado \(H\). O teorema qualitativo de persistência utiliza
positividade central de todos os prefixos e uma hipótese que fornece
existência de falha fora da reta. [SigmaFailureOrder](https://github.com/thiagomassensini/geometry-of-numbers/blob/25ba493/research/native-moving-schur-sigma/SigmaFailureOrder.lean)

## Mesmo orçamento, com a margem do prefixo explícita

Use a série de [SigmaTransverseAllOrder](../native-moving-schur-sigma/SigmaTransverseAllOrder.lean)
e a [cota da cauda](TRANSVERSE_SCHUR_REMAINDER.md), de modo que
\(H_s(d)=H_s(0)+d^2 A_s+E_s(d)\), incluindo o setor deslocado \(s=1\).
Fixe uma base real invertível \(P\), a mesma no centro, no termo
quadrático e na cauda. Defina \(B=P^\top A_s P\). Seja \(\eta\)
uma cota para \(\|P^\top E_s(d)P\|\) em \(|d|\le\delta\).
O cálculo transporta cada coeficiente de Taylor antes de tomar seu
módulo. Como os termos omitidos começam em ordem quatro, o mesmo
orçamento dá \(\|P^\top E_s(d)P\|\le t^2\eta\),
com \(t=(d/\delta)^2\).

Quando o centro é medido pelo corte material das células, use a matriz
dos mesmos momentos \(\widehat H_M\) de `observedMoment M` e
\(G_M=P^\top\widehat H_M P\). As estimativas por momento de
`ResponseTails.lean`, usadas em `CriticalTail.lean`, dão
\[
\begin{aligned}
|[P^\top (H_s(0)-\widehat H_M)P]_{ij}|
 &\le \sum_{a,b}|P_{ai}P_{bj}|\,
     \texttt{responseBudget}(2(a+b+s)+1,M).
\end{aligned}
\]
A maior soma de linha é uma cota \(\epsilon\) da norma do erro.
Na direção crítica isolada, a mesma expressão vira
\(C_{\mathrm{crit}}/[4(4M-1)]\). O erro do corte \(M\) entra
como erro do centro, enquanto o deslocamento \(d\) aparece na
série transversal. [Cauda na direção crítica](../native-cell-jet-tail-bounds/CriticalTail.lean)

As duas condições finitas suficientes são
\[
G_M-\epsilon I\succ0,\qquad
G_M+\delta^2 B-(\epsilon+\eta)I\succ0.
\]
Com efeito, a combinação convexa desses dois blocos com peso \(t\)
é uma cota inferior de \(P^\top H_s(d)P\), pois \(t^2\le t\).
Isso preserva o sinal do termo quadrático e usa módulos somente no
orçamento dos erros. Na borda, uma direção negativa para
\(G_M+\delta^2 B+(\epsilon+\eta)I\) testemunha uma direção negativa
para a matriz original. Se um prefixo ainda não foi certificado,
a primeira condição é ela própria um teste de positividade central.
O mesmo raciocínio vale com observação direta do centro, tomando
\(G_M\) como \(P^\top H_s(0)P\) e \(\epsilon=0\).

A cota polarizada `all-order-polarized-tail` trata o corte do
número de direções. A cota `finite_odd_energy_absolute_tail`
trata a convergência radial de famílias ímpares fixas. Para
aplicar qualquer uma como erro adicional acima, é necessário
identificar a observação correspondente com o mesmo bloco de
momentos. Os três cortes têm parâmetros e constantes distintos.
[Obstrução ao orçamento absoluto](../all-order-polarized-tail/BudgetScale.lean)
· [Cauda radial ímpar](../native-summable-radial-tail/SummableFamily.lean)

## Certificado na faixa profunda

Os momentos centrais foram diretamente encerrados por Arb a
partir da característica completada original e os pivôs centrais
necessários foram certificados por sinal estrito. Em seguida,
a base central ortonormal deu \(G_M=I\) exatamente. A avaliação
usa o Taylor transversal e seu resto, e é conferida por Taylor
direto no deslocamento. O corte físico de células \(M\) não
é usado nesse certificado.

Para \(\delta=10^{-100}\):

- \(C_{113}(d)\succ0\) para todo \(|d|\le\delta\).
- Na borda, o primeiro pivô negativo intercalado está na
  dimensão 114, no setor deslocado de grau 56.
- O pivô na borda está encerrado pelo intervalo
  \(-1{,}69770150155\cdot10^{-467}\pm2{,}69\cdot10^{-479}\).
- No bloco \(H\) não deslocado, o primeiro pivô negativo está
  na ordem 58. O resto normalizado de ordem quatro em diante
  é inferior a \(1{,}611\cdot10^{-200}\) no setor par e a
  \(3{,}333\cdot10^{-198}\) no setor ímpar, incluindo os blocos
  usados no certificado de falha.
- O primeiro raio de falha da dimensão 114 está entre
  \((21683/32768)10^{-100}\) e \((43367/65536)10^{-100}\).
  Todo \(|d|\) até a borda inferior é positivo na dimensão 114,
  e há direção negativa na borda superior.

O verificador usa o modelo quadrático inferior em todo o
intervalo até o limite inferior do raio de primeira falha.
Usa o modelo superior para demonstrar negatividade no limite
superior. A bisseção só move um limite depois de certificar seu
respectivo sinal.

## Escala da cota material existente

Na direção mônica de grau \(n\), ponha \(r=4n+2s+1\) e
\(\kappa=\|\texttt{rJet}\ 0\ \texttt{clockMultiplier}\|>0\).
O termo \(i=j=n\) e o termo inicial do canal de relógio
dão \(C_{\mathrm{crit}}\ge(r+1)2^{r+2}\kappa\).
Portanto, para que o orçamento já publicado seja menor que
um pivô central positivo \(\sigma_{s,n}\), seria necessário
\[
\frac{16M-4}{\kappa}>
\frac{(r+1)2^{r+2}}{\sigma_{s,n}}.
\]
No setor deslocado de grau 56, o lado direito é maior que \(1{,}4874\cdot 10^{538}\).
Esse teste explica por que a cota original de células é
pouco eficiente como certificado relativo nessa ordem.

Rode na VM, na raiz desta worktree:

```bash
/home/thlinux/miniforge3/bin/python3 research/projective-chiral-complex-cauchy/certify-transverse-schur.py --deep
```

A opção profunda usa 6144 bits para o cálculo de momentos e
congruências e seis termos transversais antes da cauda. As
comparações na base normalizada usam operações por intervalos
com 256 bits. As desigualdades são analíticas, e os certificados
numéricos finitos usam Arb. A prova de positividade central de
todos os prefixos e uma lei de crescimento para o raio certificado
permanecem em aberto.
