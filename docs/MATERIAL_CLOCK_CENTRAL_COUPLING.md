# Acoplamento central do relógio material e residual Green canônico

## Resultado

Formalizamos a dinâmica forçada do complemento central da fonte material
completada, seus cruzamentos Green e a identidade assinada que os reúne no
residual canônico real. O acoplamento vem do estado central efetivo e conserva
o contraste material `log 2 / sqrt 2` da primeira aresta.

**A positividade do residual e de toda a hierarquia continua aberta.** Não
construímos uma órbita unitária para o relógio completado, uma nova métrica
ou um Gram ajustado. A decomposição torna explícitos os canais do mesmo
problema; não melhora por si só os sinais dos coeficientes `C_k`.

Base geometry: `3d1ec130ed2c819494050b324be4d4632249aef8`, merge do PR #15.
Operador consultado sem alterações: `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
Proveniência e pins: `research/material-clock-coupling/provenance.json`.

## 1. Objetos existentes e distinções necessárias

Usamos o mesmo estado
\(Y_t=\texttt{baseTwoCompletedBoundaryHilbertState}\ t\), com semente,
gradientes e retorno global. O relógio é o `completedBoundaryTransportedClock`
no domínio de grafo já construído: retorno igual à soma das células,
interior clockado em l2 e retorno clockado somável.

O domínio não foi ampliado. O relógio continua não simétrico na métrica
produto existente; os no-gos de auto-adjunção e intertwiner isométrico
permanecem válidos.

Sejam `P` a projeção na linha complexa do estado central, que conserva
as duas quadraturas reais, `Q=I-P` e \(e=Y_0/\|Y_0\|\). Essa projeção é diferente da
projeção do readout `semente + retorno global`. Chamaremos o complemento
deste último de `H`; não identificamos `H` com `Q`.

A notação complexa abaixo conserva as duas quadraturas originais. Os mapas
de projeção são os mapas complexo-lineares existentes, portanto também reais
lineares. Nenhum carrier novo substitui a geometria real.

## 2. Um único vetor de acoplamento, determinado pela fonte

Definimos coordenadas e componentes do relógio existente:

\[
\gamma(y)=\frac{\langle e,y\rangle}{\|Y_0\|},\qquad
b=QLY_0,\qquad Z_t=QY_t,\qquad A_t=QL(QY_t).
\]

`L(QY_t)` é tipado pela preservação de domínio já provada. Não supomos que
o resultado pertença novamente ao domínio de `L`, nem iteramos `L`.
O fator em `gamma` apenas reexpressa a projeção já normalizada:

\[
Py=\gamma(y)Y_0,\quad\gamma(Y_0)=1.
\]

Para **todo** argumento do domínio original, Lean verifica

\[
Ly=L(Qy)+\gamma(y)LY_0,\qquad
\boxed{QLy=QL(Qy)+\gamma(y)b.}
\]

Assim o bloco central-para-complemento tem imagem na linha do vetor `b`.
Esse vetor não foi escolhido para fornecer um sinal desejado:

\[
\boxed{\texttt{carryMaterialCentralEdgeContrast}(b)
       =\log2/\sqrt2,\qquad b\ne0.}
\]

A não anulação reutiliza a cota física anterior \(\|b\|^2>1/32\).
O retorno global permanece no relógio e no produto interno do carrier inteiro.

## 3. Dinâmica forçada, com uma derivada Hilbert efetivamente disponível

Usando a derivada forte de primeira ordem já provada para `Y`, obtivemos

\[
\boxed{Z'_t=-i\bigl(A_t+\gamma(Y_t)b\bigr).}
\]

Na origem:

\[
Z_0=0,\quad A_0=0,\quad Z'_0=-ib\ne0.
\]

Portanto o complemento não é uma evolução linear autônoma de seu estado
inicial zero. O centro alimenta o complemento. Esta conclusão é sobre o
candidato e a projeção especificados; não é um no-go para toda realização.

Não foram postuladas derivadas fortes adicionais do estado global. A ordem
de um jet canônico não foi identificada com tempo, profundidade ou câmera.

## 4. O companheiro recebe o mesmo acoplamento e o dressing completo

Escreva `D(t)` para `baseTwoCanonicalDressingScalar` e `X_t` para o par
companheiro/duas vezes o valor já existente. Com a convenção original

\[
G((c,v),(\tilde c,\tilde v))
=\langle v,\tilde c\rangle-\langle c,\tilde v\rangle,
\]

o complemento componente a componente tem reconstrução exata:

\[
\mathbf QX_t=K_t+F_t^{\rm forc},
\]
\[
K_t=(iD_tA_t-D'_tZ_t,\ 2D_tZ_t),\qquad
F_t^{\rm forc}=(\lambda_tb,0),\quad\lambda_t=iD_t\gamma(Y_t).
\]

Os dois argumentos permanecem independentes:

\[
\boxed{G(\mathbf QX_t,\mathbf QX_u)=G(K_t,K_u)+
2i\overline{D_t}D_u\bigl(
 \gamma(Y_u)\langle Z_t,b\rangle+
 \overline{\gamma(Y_t)}\langle b,Z_u\rangle\bigr).}
\]

Também expandimos `G(K_t,K_u)` com a conexão derivativa inteira:

\[
2i\overline{D_t}D_u(\langle Z_t,A_u\rangle+\langle A_t,Z_u\rangle)
+2(\overline{D'_t}D_u-\overline{D_t}D'_u)\langle Z_t,Z_u\rangle.
\]

Não há hipótese de simetria de `L` nessa conta.

## 5. Calibração de um cruzamento genuíno na origem

A parcela comprimida `K_0` é zero, mas a companheira forçada permanece.
Lean demonstra, sem dividir por `u`,

\[
G(\mathbf QX_0,\mathbf QX_u)=
2i\overline{D_0}D_u\langle b,Z_u\rangle,
\]

\[
\boxed{\frac{d}{du}G(\mathbf QX_0,\mathbf QX_u)\big|_{u=0}
=2|D_0|^2\|b\|^2>0.}
\]

É a derivada de um **cruzamento Green**, não uma energia diagonal, um momento
canônico ou uma prova de positividade de kernel. Ela certifica que o canal
de acoplamento participa efetivamente do primeiro cruzamento.

## 6. A redução faz aparecer a parcela quadrática do acoplamento

Para a redução existente \(T_t(c,v)=(c-atv,atc)\), com `a` a escala original,

\[
G(F_t^{\rm forc},F_u^{\rm forc})=0,
\]
mas

\[
\boxed{G(T_tF_t^{\rm forc},T_uF_u^{\rm forc})
=-a(u-t)\overline{\lambda_t}\lambda_u\langle b,b\rangle.}
\]

A fórmula vale inclusive nas colisões, onde o fator se anula. Antes da redução
o self-Green nulo não autoriza apagar esse canal. Depois dela é necessário
preservar os dois cruzamentos ordenados e essa parcela quadrática assinada.

## 7. Identidade com o residual canônico: o que foi fechado

Escreva `Xred_t=T_t X_t`. A nova síntese Green é

\[
\begin{aligned}
\mathcal B(t,u)={}&G(\mathbf P X^{red}_t,\mathbf P X^{red}_u)
+G(T_tK_t,T_uK_u)\\
&+G(T_tK_t,T_uF_u^{\rm forc})
+G(T_tF_t^{\rm forc},T_uK_u)\\
&+G(T_tF_t^{\rm forc},T_uF_u^{\rm forc})
-G(\mathbf H X^{red}_t,\mathbf H X^{red}_u).
\end{aligned}
\]

Reutilizando a identificação da fonte e a identidade assinada do PR #8,
a comparação externa verifica numa vizinhança da origem:

\[
\boxed{\mathcal B(t,u)=
2a^2tu\,\overline{F(t)}F(u)(u-t)R(t,u),}
\]

onde `F=baseTwoCanonicalResponse` e `R=carryMaterialRealResidual` são as
respostas **já existentes**. A realidade de `R` foi reutilizada, não postulada.
Aqui `F` não é a abreviatura do par de acoplamento acima.

Temos, portanto, a passagem exata:

fonte completada → relógio no domínio de grafo → acoplamento central e
complemento → companheiro com dressing → redução com cruzamentos → subtração
Green do readout oculto → **mesmo residual canônico real**.

Nenhum momento foi redefinido e nenhum kernel foi escolhido como Gram-alvo.
O residual alcançado é o mesmo cuja extração em ordens arbitrárias fornece
os `C_k` do PR #12 e cujas integrais theta são as do PR #13.

## 8. A primeira linha exige cancelamento, não apagamento

A comparação também prova, para todo `u`, que o Green oculto na primeira linha
é exatamente a soma do Green central com os dois termos que sobrevivem:

\[
G(\mathbf H X^{red}_0,\mathbf H X^{red}_u)=
G(\mathbf P X^{red}_0,\mathbf P X^{red}_u)
+G(T_0F_0^{\rm forc},T_uK_u)
+G(T_0F_0^{\rm forc},T_uF_u^{\rm forc}).
\]

Isso usa o readout companheiro central nulo da fonte completada. Mostra
concretamente por que a componente invisível ao readout não pode ser removida
do balanço antes da síntese.

## 9. O que continua faltando para transportar positividade

A **identificação escalar assinada** acima está provada. Não falta outra
identificação de fonte nesse nível. Falta uma estimativa de coerção ou uma
realização positiva do balanço normalizado que controle conjuntamente o
central, o comprimido, os cruzamentos, o quadrático forçado e o Green oculto.

Não provamos que essa combinação seja um produto interno positivo. Também
não se pode dividir termo a termo por `tu(u-t)`: o fator se anula nos eixos e
na diagonal. O residual original fornece sua própria extensão escalar;
parcelas isoladas não receberam extensões por conveniência.

A unitariedade do relógio diagonal em outro carrier não descarrega essa
obrigação. O relógio completado atual mantém a obstrução de simetria e a
projeção central mantém seu defeito de comutação. A decomposição nova não
transforma esses fatos em preservação de uma energia positiva.

Para a hierarquia, as margens theta principais do PR #15 continuam abertas.
Nenhum sinal novo de `C7` ou de ordens posteriores foi certificado aqui.

## 10. Status e validação

| Resultado | Status |
| --- | --- |
| Acoplamento `QLy=QLQy+gamma(y)b`, no domínio original | **PROVADO em Lean** |
| Contraste material de `b`, não anulação e dinâmica forçada da fonte | **PROVADO em Lean** |
| Dressing, dois cruzamentos e termo quadrático após redução | **PROVADO em Lean** |
| Primeiro cruzamento Green e sua derivada na origem | **PROVADO em Lean** |
| Balanço acoplado igual ao numerador do residual canônico real | **PROVADO em Lean** |
| Cancelamento da primeira linha com o Green oculto | **PROVADO em Lean** |
| Evolução unitária do relógio completado na métrica atual | **OBSTRUÍDO no carrier/domínio atuais pela não simetria existente** |
| Realização positiva ou coerção do balanço normalizado | **ABERTO** |
| Positividade de toda a hierarquia, Gram global ou HP/RH | **NÃO DEMONSTRADO** |

Novo módulo: `GeometryOfNumbers/Analysis/CarryMaterialClockCentralCoupling.lean`,
com 10 definições de coordenadas/componentes e 24 teoremas. Não é um operador
alternativo. Três teoremas de comparação canônica ficam no arquivo externo
`research/material-central-calibration/CanonicalComparison.lean`.

Validação em `llm`: build focado e completo `--wfail` (completo: 8835 jobs),
auditorias Foundation/Geometry/Analysis, regressões e comparação externa com
`warningAsError`. As 37 raízes novas têm guardas transitivas de axiomas nos
tipos e corpos e `#print axioms`; somente os três axiomas padrão da análise
são permitidos. Os testes antigos da comparação foram preservados.

Os pins, a fonte, a métrica e as normalizações permanecem intactos. Os outros
repositórios foram consultados sem modificações. Não houve experimento numérico
ou dado externo usado como premissa de prova.

Fontes históricas verificadas no Git: relógio completado e sua obstrução
`ce3077323ddb32df1931c1d0c2dba12a78d72c06`; projeção central e sua calibração
`a238792acb9a07af3e753f213bbc6502b18d197b`; par companheiro e numerador Green
`b6c6d268abe8827871467409cc966d9a08a5d59b` (integrado no PR #8).
