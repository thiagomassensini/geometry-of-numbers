# Defeito bilinear TFVD/Green no balanço polarizado

O núcleo desta rodada é \(\mathcal P=\texttt{polarizedSourceBalance}\)
da fonte completada, com as duas entradas independentes. O objetivo foi
localizar o defeito que a síntese de câmera traz para o pareamento nativo
e testar a sua escala nos cruzamentos. Os pontos, os pesos HB, o carrier
Cauchy e os mapas TFVD são os da construção anterior.

## Onde a Gram entra e onde ela sai

O CSA dá \(\mathcal P/2=\langle S_c,S_d\rangle+iB(c,d)\), em que \(B\)
é `coisometricFourChannelBalance`. O escape global cancelado não constitui
margem suplementar. No GoN, a mesma \(B\) já se decompõe em
\(-i\,\texttt{variableDefect}+i\,\texttt{overlapCorrection}\).
A Gram coisométrica combinada com a correção de overlap dá a Gram
amortecida \(O\odot G\). Retomamos essas duas identidades com os mesmos
mapas. [CSA, balanço de quatro canais](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/main/CarrySelfAdjointOperator/CompletedNativeChiralReturnCoisometricSewing.lean)
· [GoN, orçamento anterior](https://github.com/thiagomassensini/geometry-of-numbers/blob/9bcec6b/research/native-jet-overlap-budget/REPORT.md)

Em coordenadas normalizadas, sejam \(z_i=i_{\mathbb C}(i+1)/(k+1)\),
\(C_{ij}=\langle v_i,v_j\rangle\) o pareamento Cauchy, e \(\theta_i\)
a normalização nativa \(1/(\sqrt2 F(z_i))\). A entrada física
é \(c_i=x_i\alpha_+(z_i)\), onde
\(\alpha_+(z_i)=\theta_i\,\operatorname{HB}_+(z_i)\) já é a amplitude
do jet nativo. Seja \(u_i\) o estado enriquecido TFVD no ponto \(z_i\),
e \(G_{ij}\) o pareamento ambiente já com a normalização \(\theta\).
Definimos
\[
\Pi_{ij}=O_{ij}G_{ij}, \qquad
D_{ij}=\overline{\theta_i}\theta_j C_{ij}\,
   \texttt{defectPair}(z_i,z_j,u_i,u_j),
\quad
O_{ij}=\frac{2\sqrt{(i+1)(j+1)}}{i+j+2}.
\]
O último fator de \(D_{ij}\) é o defeito existente das portas transportadas,
com os dois argumentos originais. A fórmula verificada é
\[
\tfrac12\mathcal P(c,d)=\sum_{i,j}\overline{x_i}y_j(\Pi_{ij}+D_{ij}).
\]
No domínio regular, cada entrada \(\Pi_{ij}+D_{ij}\) coincide com o
divided slope completado.

O split traço/fibra revela por que a Gram sozinha não fecha. A identidade
prévia `defectPair_signature` é a assinatura quiral do traço menos a
fibra com escala \(\sqrt{2\Im z_i}\sqrt{2\Im z_j}\). A multiplicação pelo
Cauchy converte essa escala exatamente em \(O_{ij}\). Assim,
\[
D_{ij}
=\overline{\theta_i}\theta_j C_{ij}
  \bigl(\langle T_{+,i},T_{+,j}\rangle-\langle T_{-,i},T_{-,j}\rangle\bigr)
-\Pi_{ij}.
\]
Os \(T_{\pm,i}\) são as leituras quirais do traço do mesmo estado \(u_i\).
**A fibra negativa de \(D\) cancela a Gram amortecida inteira, entrada a
entrada.** Sobra a assinatura em dois argumentos do traço TFVD completado.
Esta localização é para o defeito bilinear Green. Ela não identifica
`defectPair` com o cumulante escalar de massa conectado pré-completamento
do repositório primos.

## O teste radial é mais forte que o teste de ordem zero

Use a subsequência cofinal \(k_\nu=2(N+1)(\nu+1)-1\) na malha original.
Ela alinha exatamente as malhas de projeção e de resposta ambiente
já publicadas. Para \(N\) fixo, os limites são
\[
\Pi_{ij}\longrightarrow A_0 O_{ij},\qquad
D_{ij}\longrightarrow h_0-A_0 O_{ij},
\quad A_0=\|\texttt{NormalizedAmbientResponseState}(0)\|^2.
\]
A positividade estrita \(A_0>h_0>0\) vem de resultados existentes, sem
hipótese de positividade do fechamento Green. O antigo teste de \(N=1\)
recupera \(h_0-A_0\). [CSA, excesso central](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/main/CarrySelfAdjointOperator/CompletedNativeAmbientRadialIntertwiningNoGo.lean)

Para qualquer entrada fixa \(x\ne0\) com \(\sum_i x_i=0\), o termo constante
\(h_0|\sum_i x_i|^2\) some. A injetividade dos vetores Cauchy observados
dá \(L=A_0\|\sum_i x_i o_i\|^2>0\), onde \(\langle o_i,o_j\rangle=O_{ij}\).
Logo
\[
\Pi(x,x)\longrightarrow L,\qquad
D(x,x)\longrightarrow-L,\qquad
-\frac{\Re D(x,x)}{\Re\Pi(x,x)}\longrightarrow1.
\]
Em particular, os stencils de diferenças de toda ordem positiva, inclusive
os pares, consomem exatamente a margem dominante. Uma cota com folga
fracionária fixa \(D(x,x)\ge-(1-\varepsilon)\Pi(x,x)\), \(\varepsilon>0\),
falha nessas direções no refinamento.

Para ver a escala no primeiro stencil par, tome \(x=(1,-2,1)\) e
\(t=1/(k+1)\). O limite da razão acima vale por \(\sum x_i=0\).
O limite de diferenças mistas já disponível dá
\((\mathcal P(c,c)/2)/t^4\to4h_2\).
Ao eliminar também o cruzamento com a âncora \(e_0\) pela própria forma
\(\mathcal P/2\), o termo de \(t^4\) passa a \(4(h_2-h_1^2/h_0)\).
Essa última leitura é a aplicação analítica do stencil ao bloco de
coeficientes confluentes. Ela distingue a energia dominante do carrier,
que se cancela, do coeficiente que precisa ser controlado pela fonte.

## Fronteira de sinal

As identidades encontram o pedaço que impede a Gram de câmera de ser a
Gram do alvo. A desigualdade que sobra envolve o confronto dos dois
pareamentos do traço completado, primeiro nas direções pares após
eliminação dos cruzamentos. A positividade desse traço em ordem
arbitrária segue em aberto. A positividade de uma diagonal isolada ou
dos dois Grams quirais tomados individualmente não dá essa comparação.

`ConnectedDefectLimit.lean` registra a identidade polarizada, o split
exato traço/fibra, o limite de cada entrada e a razão limite nas direções
de soma nula. Nenhum dado sobre zeros entra nas identidades.

### Validação na VM

A verificação usa o ambiente Lean 4.32 do CSA e os módulos físicos
preexistentes já compilados no GoN. No servidor `llm`, a ordem das
dependências locais no `LEAN_PATH` é a mesma de
`research/native-jet-overlap-budget/compile_module.sh`. O módulo novo
foi verificado diretamente com `-DwarningAsError=true`. As auditorias
das declarações novas usam `propext`, `Classical.choice` e `Quot.sound`.
