# Cruzamento Green finito e compensação física do jet zero

**Alvo da PR #83 cumprido. Resultado global: PARTIAL.**
A fórmula finita, os dois limites separados e a compensação eventual C2
foram formalizados. A positividade canônica em todas as ordens segue aberta.

24/10/2026. `thiagomassensini/geometry-of-numbers`.
Branch `agent/finite-green-crossing`, base PR #83,
`a2b8aeadff77c0be17a09263a0e188f1c57a46d4`.
`origin/main` foi conferida em
`59e53d863f4ef0ad998b0eb19fd3891c9839cc35`.
Entrega em draft, sem merge automático. Nenhuma fonte, métrica ou pin alterado.

## A — O que já estava demonstrado

A PR #81 fornece as isometrias de potência no carrier Cauchy original,
o refinamento comum, o pareamento de duas entradas e os jets canônicos.
A #82 transporta o avanço e o Green originais, conserva dois bordos e o
numerador residual completo e prova a anulação do setor residual–residual
na seção regular, sem apagar os cruzamentos.

A PR #83 fornece a identidade média–contraste e a desigualdade
`greenBudget (1/Real.sqrt 2)>1/2`. A identificação desse integral com cada
setor Green ainda era apenas sugerida pelos diagnósticos numéricos.

Reutilizamos `physicalGreenResolvent`, `intervalMultiplier_toLp`,
`physicalCompletedFiniteGreen_reconstruct`, as features literais
`sqrt(x)*x^j`, `normalized_chiral_gap` e a fonte projetiva original.
Não construímos vetores a partir dos momentos ou de uma fatoração da Hankel.

A positividade de `h0` é um certificado **anterior**:
`canonicalCompletedNativeLogDerivativeMoment_zero_pos`, em
`CompletedC3FullWronskianCentralChiralEnergy.lean`. Sua proveniência é o
fechamento theta/cosseno de baixa ordem já existente. Essa dependência
permanece explícita; não anunciamos uma nova demonstração puramente
geométrica de `h0>0`.

A PR #41 permanece uma draft independente. Sua energia de bordo residual
igual a `4 ×` pivô não foi importada como se estivesse integrada, nem foi
confundida com o residual TFVD estudado aqui.

## B — O que foi demonstrado agora

Os nomes novos estão em `CarryFiniteGreen`.

### B.1 — Domínio, objetos e normalizações originais

Usamos `k` somente como índice da regularização radial e escrevemos
`kappa=k+1`. Ele não é a profundidade vertical da nota centro–pernas.
Os dois nós são `z0=i/kappa`, `z1=2i/kappa`.

Sejam `R=-F'/(2F)`, `deltaR=R(z1)-R(z0)` e
`a_k=(2/sqrt(2))*sqrt(kappa)`. Esse último coeficiente já pertence à
normalização quiral e radial original; não é um parâmetro ajustado.

A forma nativa é

\[
\Phi(X,Y)=\tfrac12(\langle X_+,Y_+\rangle-\langle X_-,Y_-\rangle).
\]

`eta` é o peso do Green. `A` é o antigo multiplicador por `x` no carrier
físico, e `G=(I-eta A)^{-1}` é o resolvente original identificado na #82.
Esse `A` não foi identificado com o clock material ou com a Jacobi.
As fórmulas finitas usam `0<eta<1` e os denominadores nativos `F,E+`
não nulos nos dois nós. Nenhuma hipótese de sinal é exigida nessa camada.

### B.2 — O cancelamento do numerador foi provado antes do pairing

Para `e0=initialInput`, `initial_bulk` e `initial_shift` demonstram:

\[
\mathrm{bulk}(e_0)=\eta e_1,\qquad Se_0=e_1.
\]

`residual_numerator_initial` então demonstra exatamente:

\[
\boxed{N_\eta(e_0)=(2I-\eta A)\mathcal E(e_0).}
\]

Os termos `eta E(e1)` provenientes do bulk e do shift residual se
cancelam **na identidade completa**. Não foram truncados nem omitidos.
Os dois traços continuam no termo de bulk reconstruído.

`normalized_positive_response`, `residual_initial_first` e
`residual_initial_pair` extraem as duas coordenadas originais:

\[
\mathcal E(e_0)=a_k\,\delta R\,(\varphi_1,\varphi_1).
\]

A igualdade das pernas reutiliza o teorema nativo de gap constante.
As condições são somente regularidade dos pontos, descarregada
eventualmente pelos resultados preexistentes.

### B.3 — J é um produto interno físico efetivo

`greenPort` é definida exclusivamente pelos operadores originais:

\[
P_\eta=\eta G^2(2I-\eta A)\varphi_1.
\]

`green_port_toLp` identifica esse vetor, no Lp original, com a aplicação
dos mesmos multiplicadores à feature contínua original.
`green_port_profile_apply` deriva sua expressão ponto a ponto:

\[
P_\eta(x)=\frac{\eta(2-\eta x)}{(1-\eta x)^2}\sqrt{x}\,x.
\]

Só depois da identidade vetorial, `green_port_inner` demonstra:

\[
\boxed{\langle\varphi_0,P_\eta\rangle
 =\int_0^1x^2\frac{\eta(2-\eta x)}{(1-\eta x)^2}\,dx=J_\eta.}
\]

A passagem do integral do subtipo `[0,1]` para o integral de intervalo
conserva a medida original. O integral não foi escolhido para caber no
pareamento; foi calculado a partir da ação do resolvente físico.

`reconstructed_residual_initial` conclui a identificação vetorial completa:

\[
\boxed{\widehat E_k=a_k\,\delta R\,(P_\eta,P_\eta).}
\]

A apresentação é `m=0` da família de refinamentos existente. Os
pareamentos permanecem sob isometrias físicas comuns da #81/#82.

### B.4 — Fórmulas exatas em escala finita

Seja `X_k` a fonte inicial original e `Bhat_k` o bulk com seus dois bordos,
reconstruído pelo Green. `initial_green_split` prova
`X_k=Bhat_k+Ehat_k` e `initial_residual_self` prova `Phi(Ehat,Ehat)=0`.

`initial_source_residual_pairing` e `initial_mixed_pairing` demonstram a
identidade **complexa**:

\[
\boxed{\Phi(X_k,\widehat E_k)
 =\Phi(\widehat B_k,\widehat E_k)
 =-i\,\kappa\,\delta R\,J_\eta.}
\]

Não é necessária uma hipótese de que os valores da resposta sejam
imaginários puros. As duas quadraturas são conservadas até esse ponto.

`initial_mixed_real`, `initial_source_energy` e `initial_bulk_real` dão:

\[
\boxed{BE_k=\kappa\operatorname{Im}(\delta R)J_\eta,}
\]
\[
\boxed{\operatorname{Re}\Phi(X_k,X_k)
 =\kappa\operatorname{Im}R(z_0),}
\]
\[
\boxed{BB_k=\kappa\operatorname{Im}R(z_0)
             -2\kappa\operatorname{Im}(\delta R)J_\eta.}
\]

Aqui `BE` designa a parte real de `Phi(Bhat,Ehat)`. A parte real do
cruzamento oposto é igual por simetria Hermitiana. Portanto o balanço total
é `BB+BE+EB=BB+2BE`, preservando seus coeficientes originais.

### B.5 — Limites e sinal em C2

`scaled_increment_dslope` e `scaled_response_dslope` usam a diferença
dividida total, válida inclusive em colisões. A analiticidade já provada
da resposta e `native_derivative_zero` identificam os limites:

\[
\kappa\delta R\longrightarrow ih_0,\qquad
\kappa R(z_0)\longrightarrow ih_0.
\]

`mixed_energy_limit` e `bulk_energy_limit` concluem, separadamente:

\[
\boxed{BE_k\to h_0J_\eta,\qquad BB_k\to h_0(1-2J_\eta).}
\]

Não é uma conclusão extraída apenas do limite da soma. Cada parcela
recebeu sua identidade finita e seu próprio limite.

No peso crítico C2, a #83 já prova `J>1/2`. Com o certificado antigo de
`h0>0`, `c2_canonical_eventually_compensates` demonstra que, eventualmente:

\[
\boxed{BB_k<0,\quad BE_k>0,\quad -BB_k<2BE_k.}
\]

Assim o termo misto duplo compensa estritamente o bulk negativo. O
resultado é eventual, sem cutoff numérico explícito. Não afirma monotonia.
Os lemas anteriores de sinal recebem `h0>0` explicitamente; o último
corolário fornece o certificado preexistente, sem pressupor novos pivôs.

## C — Contexto centro–pernas: o que ajuda e o que não se identifica

Foi lido integralmente o arquivo recebido, cujo SHA256 está em
`evidence/input-context.json`. Ele foi tratado como contexto matemático,
sem adotar sua conjectura de transporte como hipótese.

A decomposição material proposta conserva uma correção real necessária:

\[
(c-r)^{-s}-2c^{-s}+(c+r)^{-s}
 =g^{-s}(q^{s/2}-q^{-s/2})^2+2(g^{-s}-c^{-s}),
\]

com `g=sqrt(c^2-r^2)`, `q=sqrt((c+r)/(c-r))`, `c>|r|`, `c>0`,
e potências definidas pelos logaritmos reais positivos.
A covariância sob dilatação completa e a identidade de compensação entre
energia de diferenças e curvatura das normas também conferem.

O diagnóstico independente verificou nove casos, com duas quadraturas
reais, centros/raios `(4,1),(8,2),(8,1)` e parâmetros `s=1/2+it`,
`t=0,3,14`, a 80 casas de trabalho. Preservou o contraexemplo negativo
`-Re(conj(u4)*Delta u4)<0`. Esses testes não são provas Lean.

Os teoremas atuais `centerLegForm_criticalSeed_energy_eq_mass` e
`centerLegCameraEnergy_criticalSeed_eq_mass` foram consultados com suas
hipóteses reais. Eles não identificam automaticamente seus parâmetros
recíprocos com os das posições materiais.

O exemplo `(3,4,5)` é uma segunda diferença material. Ele não resolve por
si só a tipagem do offset antipodal C2 de uma câmera balanceada ímpar.
A deformação material `q` tampouco é o peso Green `eta`.

A conexão metodológica é concreta: conservar a correção entre centros
na nota, assim como conservar o residual no Green. Mas não foi provado
que essa correção local seja o mesmo objeto que o residual TFVD, o
completamento Gamma ou o residual de Schur da #41. Igualar esses termos
por analogia seria perder a proveniência.

## D — O que continua aberto

Não foi demonstrada uma Gram positiva dos mesmos momentos em toda ordem,
nem uma lei universal de sinal dos pivôs. O resultado novo é a compensação
física do **jet zero**, a partir do Green original e do `h0` já certificado.

A positividade do Green na norma Hilbert não torna positiva a forma
assinada. Neste caso seu bulk é demonstravelmente negativo, e os
cruzamentos são indispensáveis. Descartar o residual mudaria o sinal do
objeto investigado.

A identidade com o kernel canônico e a síntese Cauchy são preexistentes.
Esta PR não prova uma isometria de todo o estado material multibase para
esse carrier. A fatoração vertical/local da nota também não fornece,
sozinha, tal transporte nem uma Gram canônica global.

## E — Próximo alvo mínimo, validação e reprodução

A próxima obrigação concreta é extrair do **mesmo numerador TFVD** as
portas para `e1` e os cruzamentos `e0/e1`, incluindo todos os traços.
Depois aplicar os coeficientes e a normalização da diferença finita
original do primeiro jet ímpar. Endereço material/radial `j=1` não é,
isoladamente, o jet de ordem 1.

O alvo é uma fórmula de pareamento completo para essa primeira direção
nova, que permita identificar o coeficiente de sinal da fonte antes de
procurar uma estimativa. Não se pressupõe que o sinal do bulk ou do
misto repita o caso zero, nem se recebe a positividade do próximo pivô.

A auditoria separa três grupos: construção física sem momentos como
entrada; identificação analítica dos limites; orientação de sinal usando
o certificado anterior de `h0`. Todas as raízes públicas têm `#print axioms`
e inspeção transitiva de tipos e corpos. As evidências registram os comandos,
hashes, módulos ancestrais, preservação das fontes e resultados dos testes.

**Validação executada:** 48 teoremas e seis definições, 54 raízes públicas.
A auditoria transitiva de tipos e corpos examinou 6.079 dependências:
34 raízes de construção sem momentos como entrada, 12 de identificação
analítica sem sinais finitos e oito da camada de sinal com o certificado
anterior de `h0`. Somente `propext`, `Classical.choice` e `Quot.sound`.

As 17 verificações passaram: módulos explícitos, fontes originais,
`lake build --wfail`, auditorias Foundation/Geometry/Analysis, dois
diagnósticos Python separados e preservação da base. Vinte e um módulos
ancestrais foram recompilados de fontes idênticas à base. Sem `sorry`,
`admit`, `native_decide` ou novos axiomas matemáticos.

Reprodução no host `llm`, a partir deste diretório:

```bash
python3 build_upstream.py > evidence/upstream-build.log 2>&1
python3 validate.py
```

O diagnóstico Green é uma avaliação independente da mesma característica
pela identificação posterior com xi; não usa tabelas de zeros ou alturas
nem reexecuta toda a síntese material. Os resíduos numéricos de 80/120 casas
não são cotas intervalares nem integram a confiança Lean.

**FIM DO RELATÓRIO — fórmula Green finita, limites e compensação eventual C2 do jet zero; positividade canônica em toda ordem aberta.**
