# Síntese da torre nativa na fonte Cauchy original

**Classificação: PARTIAL.** Foi fechada a obrigação de construir uma síntese
contínua da torre nativa inteira para a fonte física original, com cota uniforme
e sem utilizar os momentos canônicos. O transporte do balanço completado é
exato em qualquer dimensão finita. O sinal desse balanço e a positividade das
Hankel canônicas em toda ordem continuam abertos.

## A — O que já estava demonstrado

### Base e escopo

- Repositório: `thiagomassensini/geometry-of-numbers`.
- Branch: `agent/native-vertical-synthesis`.
- Base explícita: `5eb9b1a09a407636af44e1915c8d7026543a635d`, cabeça da PR #91.
- A PR #91 estava aberta e em draft; não foi presumida integrada à main.
- Main preservada: `59e53d863f4ef0ad998b0eb19fd3891c9839cc35`.
- Operador consultado sem alterações: `bfeb10fd2425400fa38139903d12bf0599f02e53`.
- Fontes, pins, estados sujos antigos e arquivos históricos foram preservados.

A expressão transcrita como “Nova Vertical” foi entendida como **norma vertical**;
“ao Word”, como **all-order**. A torre investigada é precisamente
`CPFormal.Analytic.Cp.NativeGpreTowerHilbert`, a torre real ℓ² já existente.
Ela não é identificada com o `CoreState` C2, com o clock material ou com o
índice da regularização radial.

A PR #91 havia demonstrado duas coisas distintas: a norma dessa torre controla
a leitura nativa; a recuperação contínua dos coeficientes a partir da norma
Cauchy é impossível para a porta finita investigada. Isso não excluía uma
síntese limitada no sentido **torre → fonte**. Essa era a obrigação escolhida.

Foram reutilizados os seguintes objetos do operador, sem reconstruir suas
colunas ou alterar sua métrica:

- `completedNativeChiralCauchyFeature` e
  `inner_completedNativeChiralCauchyFeature`;
- `NativeLaguerre.physicalCauchyClosure` e
  `NativeLaguerre.physicalCauchyFeature_coe`;
- `completedNativeRadialChiralCauchyState`;
- `completedNativeRadialChiralMultiplierState` e o quociente quiral completado;
- `canonicalCompletedNativeRadialChiralMultiplierDefectMatrix`;
- `ChiralReturn.radialIncidentSynthesis_injective`;
- `RealQuadrature.Space` e `RealQuadrature.J`.

A PR #41 continua fornecendo a distinção entre ortogonalização algébrica,
inversibilidade do prefixo e sinal do residual de Schur. Nenhum desses sinais
foi usado na construção presente. Os certificados finitos H6/K6 e as doze
fontes não foram usados para fabricar os estados desta investigação.

## B — O que foi demonstrado agora

Todos os nomes abaixo pertencem ao namespace `CarryVerticalSynthesis`.
As declarações completas estão nos arquivos Lean e em `public-roots.json`.

### 1. Cota uniforme para as colunas físicas

O carrier permanece

\[
\mathcal C=L^2([0,1],\mathbb C),\qquad
\phi_j(u)=\sqrt u\,u^j,\qquad
\langle\phi_i,\phi_j\rangle=\frac1{i+j+2}.
\]

Para qualquer suporte finito real, o Lean demonstra

\[
\boxed{\left\|\sum_j c_j\phi_j\right\|_{\mathcal C}^2
  \le 4\sum_j c_j^2.}
\]

Teoremas: `cauchy_weight_step`, `cauchy_weight_row_range`,
`cauchy_weight_row`, `cauchy_quadratic_bound`, `finite_source_pairing` e
`finite_source_bound`.

A prova usa o majorante telescópico

\[
\frac1{(i+j+2)\sqrt{j+1}}
\le 4\left(
\frac1{\sqrt{i+1}+\sqrt j}
-\frac1{\sqrt{i+1}+\sqrt{j+1}}\right)
\]

e uma desigualdade quadrática ponderada. Os pesos auxiliares aparecem somente
na prova da estimativa; não substituem a norma vertical, a amplitude geométrica
ou os pesos da fonte. A constante 4 independe da ordem, dos coeficientes e dos
momentos. Não foi obtida por ajuste numérico.

### 2. Síntese na torre inteira

Foi construído o mapa real linear contínuo

\[
S:\mathrm{NativeGpreTowerHilbert}\longrightarrow\mathcal C,
\qquad Se_j=\phi_j,\qquad \boxed{\|S\|\le2}.
\]

`nativeSynthesis` é a extensão da síntese literal de suporte finito pela
densidade dessa mesma torre. `finiteTower` e `finiteSource` são portas de
suporte finito para a extensão; mantêm as coordenadas e as colunas existentes.
Não são uma nova torre, uma nova característica ou uma realização escolhida
a partir dos momentos desejados.

Teoremas centrais:

- `finite_tower_apply` e `finite_tower_norm_sq`: coordenadas e norma originais;
- `finite_tower_dense`: densidade dos suportes finitos;
- `native_synthesis_finite` e `native_synthesis_column`: coincidência literal;
- `native_synthesis_bound` e `native_synthesis_opNorm`: cota uniforme;
- `native_synthesis_hasSum`: a soma vetorial converge para `S X`;
- `native_synthesis_unique`: unicidade entre mapas contínuos com essas colunas;
- `native_synthesis_mem_original_closure`: a imagem continua na closure física
  original, não em outro espaço completado com métrica escolhida.

Não se usa uma soma de momentos para definir `S`. Não se recebe `PosDef`,
`PosSemidef`, whitening ou sinal de pivô como hipótese.

### 3. Duas quadraturas e cruzamentos preservados

No espaço real original de duas quadraturas foi construído

\[
S_2(X,Y)=SX+iSY,\qquad
\|S_2(X,Y)\|^2=\|SX\|^2+\|SY\|^2,
\qquad \boxed{\|S_2\|\le2}.
\]

`quadrature_synthesis_pairing` conserva os quatro pareamentos ordenados de
dois estados independentes. `quadrature_synthesis_J` prova o entrelaçamento
com a rotação real `J`. `quadrature_synthesis_hasSum` fornece a soma vetorial
com os coeficientes complexos completos.

`quadrature_synthesis_finite` recupera exatamente
`∑ j, c j • completedNativeChiralCauchyFeature j`. O teorema
`finite_quadrature_synthesis_injective` reutiliza a injetividade física já
demonstrada: nenhuma direção independente de coeficientes finitos é apagada.
O nível zero permanece na construção. A sua coordenada é o traço
desingularizado, não o valor bruto da meia densidade em `u=0`.

### 4. Prefixos e caudas

`native_synthesis_difference_bound` controla a diferença de dois estados pela
norma da diferença na torre. `native_synthesis_pairing_head_tail` mantém
exatamente HH, HT, TH e TT, em dois argumentos independentes.

`native_synthesis_prefix_tendsto` e
`native_synthesis_prefix_pairing_tendsto` demonstram convergência dos vetores
e dos pareamentos dos prefixos para a mesma síntese infinita. Essa coerência
vem de uma única aplicação contínua; não de realizações finitas escolhidas
separadamente. Trata-se do kernel Cauchy original, ainda não da Hankel canônica.

### 5. Transporte do retorno completado original

Para qualquer dimensão `N`, índice radial `k` e coeficientes complexos
independentes `c,d`, `radial_incident_vector` e `radial_return_vector` provam
as igualdades dos **vetores**, antes do pairing:

\[
I_k(c)=\sqrt{k+1}\,S_2(c),\qquad
R_k(c)=\sqrt{k+1}\,S_2(cQ_k),
\]

onde `S₂(c)` abrevia a síntese das duas torres reais dos coeficientes e
`Q_k(j)` é exatamente o quociente quiral completado no ponto radial original.
O índice radial não foi identificado com profundidade vertical.

`completed_native_tower_pairing` demonstra então

\[
\begin{aligned}
\langle I_k(c),I_k(d)\rangle-\langle R_k(c),R_k(d)\rangle
&=\sum_{i,j}\overline{c_i}d_j\,D^{\mathrm{native}}_{k,N}(i,j),\\
D^{\mathrm{native}}_{k,N}(i,j)
&=\frac{k+1}{i+j+2}
  \bigl(1-\overline{Q_k(i)}Q_k(j)\bigr).
\end{aligned}
\]

`D` é a matriz existente, não uma matriz substituta. Todos os cruzamentos,
o retorno e o completamento contido em `Q` permanecem na identidade. Não foi
substituído o retorno original pela contração prima da torre.

## C — O que foi refutado

`native_center_energy` calcula a energia da coluna central:

\[
\|e_0\|_{\mathrm{torre}}^2=1,\qquad \|Se_0\|_{\mathcal C}^2=\tfrac12.
\]

`native_synthesis_not_isometry` refuta a interpretação desta síntese como
isometria. Não existe aqui autorização para transportar literalmente uma
estimativa de contração da métrica vertical para a métrica Cauchy.

`equal_vertical_norm_negative_synthesized_balance` dá o teste exato

\[
\|e_1\|=\|e_0\|,\qquad
\|Se_1\|^2-\|Se_0\|^2=\tfrac14-\tfrac12=-\tfrac14.
\]

Esse teste não é um contraexemplo ao retorno físico nem à sequência canônica.
Ele refuta somente a inferência de que a comparação das normas verticais,
sozinha, determine a comparação das energias sintetizadas. O no-go anterior
de recuperação contínua permanece compatível com a nova síntese limitada.

## D — O que permanece aberto

A norma vertical **serve**: produz agora a fonte física por um mapa limitado
em toda a torre e controla suas caudas vetoriais. A conclusão é mais forte que
um experimento de dimensão finita. Ela não é uma prova all-order dos momentos.

O kernel positivo disponível antes do retorno tem entradas `1/(i+j+2)`.
O kernel completado contém ainda `1-conj(Q_k(i))*Q_k(j)`.
Não foi demonstrado que esse fator produza uma forma não negativa nas direções
nativas relevantes, nem que o balanço seja uma única norma positiva.

O fechamento do sinal exige a métrica efetivamente induzida pela síntese:
comparar `‖S₂(c Q_k)‖` com `‖S₂(c)‖`. A estimativa `‖S₂ c‖≤2‖c‖` é superior;
não fornece a cota inferior que permitiria deduzir essa comparação de uma
contração na norma vertical. Receber a comparação desejada como hipótese
apenas reformularia o sinal, sem demonstrar sua causa geométrica.

Também não foram demonstrados nesta rodada:

- injetividade da síntese na torre infinita inteira; a recuperação contínua
  coincidente com a porta finita já havia sido refutada na PR #91;
- domínio infinito e limitação do multiplicador `c↦c Q_k` nessa torre;
- identificação entre o estado `G_pre` e o estado global C2 sem uma porta própria;
- uma família positiva cuja Gram inteira seja `h_(i+j)` e `h_(i+j+1)`;
- positividade canônica de toda ordem ou identificação espectral de alturas.

O resultado não depende de calcular novos momentos, de zeros ou alturas, nem
de uma certificação theta de sinais finitos. A identidade dos momentos com a
fonte original continua sendo a já existente; não foi alterada.

## E — Próximo passo mínimo e reprodução

A obrigação de extensão deixada pela PR #91 foi resolvida. O próximo teste
físico é agora concreto: transportar a equação TFVD/Green original, em dois
argumentos independentes, por esta `S₂` já construída, e calcular a diferença
entre o retorno ali obtido e o **mesmo** multiplicador completado `c Q_k`.

O teste começa no suporte finito denso e nas primeiras colunas, preservando
o bordo e a coordenada zero; se a identidade sobreviver, a cota uniforme
presente permite tratar a síntese das caudas. A passagem do retorno infinito
exigirá ainda provar seu domínio. Uma identidade com defeito deve conservar
esse defeito; não deve ser declarada igualdade ajustando fonte ou métrica.

Isso é uma obrigação de proveniência a testar, não uma hipótese nova de
positividade. Se o defeito não desaparecer, será preciso obter seu controle
relativo pela própria equação física. A lei de sinal geral não foi presumida.

Comandos, no servidor `llm`, no diretório desta investigação:

```bash
python3 validate.py
```

O script compila explicitamente os novos módulos com `warningAsError=true`,
executa `lake build --wfail` dos módulos físicos reutilizados e da raiz,
e roda as auditorias Foundation, Geometry e Analysis.

`Audit.lean` contém `#print axioms` para todas as raízes públicas e visita
transitivamente tipos e corpos, incluindo auxiliares privados. Permite somente
`propext`, `Classical.choice` e `Quot.sound`; rejeita dependência da sequência
canônica de momentos ou de certificados posteriores de positividade finita.
Os números efetivos e o resultado de cada comando estão em
`public-roots.json`, `evidence/lean-Audit.log` e `evidence/validation.json`.

Nesta execução passaram os 15 comandos registrados. São 37 teoremas e cinco
definições públicos novos; as 42 raízes possuem 5.669 dependências transitivas
de tipos e corpos, com somente os três axiomas fundacionais permitidos.

`evidence/source-provenance.json` registra base, fontes e pins;
`evidence/preservation.json` registra a preservação dos arquivos e estados
anteriores. Nos logs textuais são removidos somente espaços finais; quando
isso ocorre, o log bruto integral fica preservado em `.raw.log.gz`, com hash
e transformação registrados em `validation.json`.
A entrega é uma PR draft sobre a PR #91, sem merge automático.

**Conclusão:** existe agora uma síntese limitada da torre nativa para a fonte
original, coerente em todas as ordens e compatível com o par completado finito.
A positividade do balanço canônico não decorre só dessa limitação. A pergunta
de sinal permanece localizada no retorno e em seu defeito físico completo.

**Fim do relatório.**
