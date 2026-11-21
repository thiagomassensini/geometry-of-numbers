# Sinal correlacionado de Schur — fonte C3 completada, TFVD e Green

**Data:** 20/11/2026
**Repositório:** `thiagomassensini/geometry-of-numbers`
**Branch:** `research/c3-correlated-schur-tfvd-20261120`
**Estado:** teoremas Lean algébricos e de cauda compilados; certificados **intervalares externos** Arb até as ordens testadas; **nenhuma prova nova de positividade all-order**.

## 1. Proveniência e identidade dos objetos

A investigação começa na geometria posicional e na segunda diferença centrada C2. A carta Genuine é uma síntese posterior de seed, centros e pernas; a característica completada é **F=A·N**. Este módulo trabalha com os jatos de **F completada**, identificados por provas nativas anteriores com os coeficientes `nativeC` e os momentos `nativeH`. Não chama bracket, Genuine e F do mesmo objeto; C3 é apenas uma carta canônica de cálculo.

Na direção de Schur mônica `v=(v₀,…,vₙ₋₁,1)`, p é o pivô novo e `a=vₙ₋₁`; com `rᵢ=(i−n)vᵢ` definimos

\[
B=v^\top H_{s+1,n+1}v,\quad
R=r^\top H_{s+1,n}r,\quad
u=\sum_{i<n}r_i h_{s+1+i}.
\]

O teorema Euler–Schur anterior fornece, **na fonte original**,

\[
W=\alpha B-\beta ap+4R,\qquad
\alpha=(2n+s+1)(4n+2s+3),\quad
\beta=16n+8s+6.
\]

Esta frente estima a combinação **assinada** `S=αB−βap` antes de tomar módulos. A positividade do prefixo **anterior** implica `u²≤hₛ₊₁R`; uma margem certificada para a cabeça de S e a cauda conclui W>0. **W>0 é curvatura transversal**, não é o próprio sinal do pivô p.

## 2. Provas anteriores: ordem 7 já existia

| Questão | Declaração Lean | Estado |
| --- | --- | --- |
| Fonte central, setor par, matriz **7×7** positiva definida | `CarrySeventhEven.even_source_seven_posDef` em `research/seventh-even-centered-source/EvenSeventhCertificate.lean` | **Provado**. Caixas de momentos + Cholesky em coordenadas transformadas + matriz de mudança invertível. |
| Pivô par 7º e margem integral | `CarrySeventhEven.seventh_even_pivot_pos`, `seventh_even_theta_integral_certificate` no mesmo arquivo | **Provados**. |
| Setor ímpar, matriz **6×6** positiva definida | `CarrySixthOdd.odd_source_six_posDef` em `research/sixth-odd-twelve-sources/OddTrialPositivity.lean` | **Provado**, por caixas e transformação. |
| Setor ímpar, matriz **7×7** positiva definida | `CarrySeventhOddCanonical.k7_matrix_posDef_iff_theta26_theta28_gate` em `research/seventh-odd-canonical-source/K7PivotBridge.lean`, branch `k7-odd-canonical-source` | **Equivalência condicional**; a desigualdade teta não foi demonstrada por essa declaração. |
| Gram “teta bruta” positiva em outro módulo | `thetaBoxRawTheta0_posDef`, `thetaBoxRawTheta1_posDef` em CSA/`CompletedNativeThetaBoxEighthObstruction.lean` | São certificados de um **contramodelo de suficiência**; não são automaticamente positividade do Hankel nativo logarítmico. |
| Positividade “infinita” em CSA | `canonicalCompletedNativeEvenInfiniteHankelPosDef` em `CanonicalCompletedNativeStieltjesOperator.lean` | **Condicional** à hipótese `CanonicalCompletedNativeStieltjesPositivity`; não é prova incondicional all-order. |

O símbolo `h` nas provas geométricas é `canonicalCompletedNativeLogDerivativeMoment` (`research/critical-source-return/CriticalSource.lean`), exatamente a sequência consumida aqui.

**Uso concreto da indução anterior:** na ordem n=6, o setor par tem como prefixo deslocado prévio a matriz ímpar **6×6** já provada; no setor ímpar, o prefixo H_(2,6) é submatriz principal da matriz par **7×7** já provada. Esse transporte de submatriz não foi usado para anunciar novo teorema de sinal nativo. A versão antiga de Cauchy que exigia H_(s+1,n+1) era mais forte do que necessário; a versão `NativeOldPrefixSignedGate` evita tal lacuna.

**Comparação:** a rota antiga **prova o sinal de p** em dimensões finitas por caixas da fonte e por identidades com a integral teta. Esta rota nova **controla W**, seu sinal de curvatura transversal, com o primeiro modo residual e o resto conjunto TFVD. As duas rotas compartilham a origem canônica, mas as conclusões não devem ser substituídas umas pelas outras. Em particular, W>0 sozinho não demonstra a sétima ordem ímpar positiva.

## 3. Conteúdo deste commit

`lean/`: 18 fontes Lean, incluindo:

- `NativeMixedU`, `NativeMixedCS`, `NativeSingleModeGate`: transporte verdadeiro de u para Bézout/TFVD; gate condicional inicialmente escrito numa dimensão ampliada.
- `NativeOldPrefixSignedGate`: **correção do tamanho do prefixo**. Prova o gate diretamente no prefixo deslocado **antigo de dimensão n**, sem precisar de H_(s+1,n+1) PSD. O vetor do primeiro modo é a primeira coordenada do próprio prefixo (`firstCore_weight`). Esse é o gate apropriado ao residual com último coeficiente zero; a hipótese de positividade não cresce artificialmente.
- `SignedSourceTail`, `GroupedSourceBudget`, `NativeSignedGate`: S na mesma fonte completada, HH+HT+TH+TT, orçamento conjunto, gate assinado.
- `CombinedEulerBezout`: no setor par, S é o pareamento de um único núcleo `Bezout((α−βaX)(−C′),C)`; nenhuma positividade do novo kernel é postulada.
- `C3CompletedJetBoxes`: caixa racional da cauda C3 **completada** para todo cutoff positivo e todo jato par.
- `C3TailNativeCrosswalkAny`: igualdade exata com a **cauda TFVD original menos o bordo C3 original**, em qualquer cutoff.
- `C3LinearSupport`: a resposta linear assinada depende de um **prefixo finito** de coeficientes, incluindo companion e cruzamentos.
- `C3Certified384Boxes`: quatro caixas racionais provadas em Lean para `M=384`; conservadoras.
- `AuditC3JetBoxes`: auditoria de axiomas das novas declarações.

A inspeção `#print axioms` dos teoremas centrais retorna apenas `propext, Classical.choice, Quot.sound` nas dependências inspecionadas. As fontes não usam `sorry` ou axiomas de sinal adicionais.

`numerics/`: scripts reexecutáveis, incluindo avaliação intervalar `python-flint`/Arb. `evidence/`: dados de 320 dígitos com **23 caixas de jatos** e **18 comparações intervalares** em `M=384`. `reports/`: proveniência detalhada e histórico das etapas.

## 4. Estado dos intervalos e escopo exato

No setor ímpar da ordem `n=9`, o bloco da fonte que aparece em B tem `r=n+2=11`. `C3LinearSupport.signed_linear_prefixTail` garante que bastam índices de jatos até `2r=22`; daí os **23 coeficientes** `T₀,…,T₂₂`.

Com `M=384`, a avaliação intervalar externa Arb verificou todos os gates para `s∈{0,1}` e `n∈{1,…,9}`: **18/18**. Nas ordens `n=9`, as razões assinadas são aproximadamente 0,002735 (par) e 0,111100 (ímpar); limites inferiores do primeiro modo, positividade dos prefixos anteriores e cobertura do erro também foram verificados com intervalos. Uma segunda execução com 320 dígitos confirmou a rodada de 240 dígitos.

As caixas Arb são **verificações intervalares externas**, não certidões kernel Lean. O avaliador usa a identidade clássica posterior com xi para calcular numericamente F, após a cadeia geométrica de identificação ser tratada separadamente; esta identidade **não substitui a origem da construção**. O uso de dados preexistentes dos momentos serve como conferência, não como entrada de zeros.

Os quatro limites **provados no Lean** para os jatos completados da cauda `M=384` são:

| j | Limite Lean | Limite Arb mais estreito (externo) |
| ---: | ---: | ---: |
| 0 | 2×10⁻³⁰ | 8,81×10⁻³⁷ |
| 9 | 2×10⁻¹⁹ | 2,09×10⁻³⁹ |
| 18 | 9×10⁻⁹ | 3,29×10⁻⁵¹ |
| 22 | 6×10⁻⁴ | 1,63×10⁻⁵⁷ |

## 5. Lacunas reais

Ainda faltam (a) eliminar a hipótese explícita `hCoeff` da expansão linear por impulsos, usando a localidade já provada; (b) elevar as 23 caixas finas do Arb a certificados Lean da avaliação C3 completada; (c) certificar o termo quadrático TT e as caixas das direções Schur, e então fechar **teoremas de sinal finitos** para as ordens testadas; (d) encontrar um orçamento uniformemente relativo em ordem arbitrária. **Nenhuma alegação all-order, RH ou “zeros Genuine ⇒ tilt nulo” decorre destes artefatos.**

## 6. Execução e reprodutibilidade

Os módulos foram verificados na VM **HEX-LLM-AI-01**, com Lean 4.32 e as bibliotecas/caches prévios de `geometry-of-numbers`, `carry-self-adjoint-operator`, `c3-fourteenth-tail` e `tfvd-bezout-schur-residual`. Ver `validate-vm.sh`. O script não baixa dependências automaticamente nem constitui uma compilação limpa de todas as PRs históricas.

As caixas externas podem ser recalculadas com:

```bash
python3 numerics/c3_arb_signed_gate.py 384 9 320
```

Requer `python-flint` e o arquivo de momentos da VM em `/home/thlinux/momentos/native-jet-vm-20260930/native_jet_exploration/moments512.json`. Resultados novos aparecem em `evidence/`.

**Integridade:** os checkouts com alterações preexistentes não foram mexidos; este material foi consolidado num worktree isolado e publicado em branch própria.

## 7. Atualização formal — 23 jatos e impulso correlacionado (20/11/2026)

A continuação em `lean/C3TwentyThreeBoxes.lean`, `lean/C3ImpulseLinearity.lean`,
`lean/C3ImpulseExpansion.lean`, `lean/C3JointSource384.lean`,
`lean/C3JointQuadraticBudget.lean` e `lean/C3QuadraticRational384.lean`
fecha **no kernel Lean** a expansão linear por impulsos, que antes aparecia
como a hipótese `hCoeff`, e o erro quadrático TT com **cotas de jatos
racionais provadas para todo índice**.

O teorema `original_c3_joint_source_budget384_rational` estabelece um
orçamento de erro do funcional assinado S da fonte completada genuína,
sem premissas sobre a expansão de impulsos ou o erro quadrático. O
orçamento é finito nas dimensões indicadas, mas continua conservador;
a desigualdade estrita necessária para certificar W>0 **não está fechada
por este teorema**.

Os intervalos Arb de 320 dps seguem como evidência externa, não
identificados com as caixas Lean mais largas. Ver
`reports/RELATORIO_RATIONAL_23_IMPULSOS_20261120.md`. O README original
de proveniência e a comparação teta/TFVD acima permanecem válidos.

A especialização em ordem 9 dos **dois setores originais** está em
`lean/C3NativeNineCertifiedError.lean`, com auditoria de axiomas em
`lean/AuditC3NativeNine.lean`. Esses corolários certificam o erro
assinado com os endereços distintos 10/10 e 11/10, mas **não certificam
o sinal da curvatura**.

## 8. Pesquisa sobre a inclinação e o resíduo após 100 momentos (20/11/2026)

O teste em numerics/finite_jacobi_100.py reconstrói, a partir dos momentos
armazenados, o operador de Jacobi positivo de dimensão 50 que reproduz
os primeiros 100 momentos. Arb certificou 50 pivôs positivos em H0 e
50 em H1 para as **casas decimais armazenadas**; o algoritmo de Jacobi
exibe 50 nós e pesos positivos, sem receber zeros como entrada.

O relatório reports/RELATORIO_100_MOMENTOS_RESIDUO_JACOBI_HARDY_20261120.md
explica a identidade de quadratura, a invariância do sinal ao retirar
a inclinação e a ponte **já provada** no CSA: não recorrência finita
incondicional + energia nativa do bordo PSD em todas as ordens ⇒
positividade estrita de todas as torres Hankel. A obrigação aberta é
a não negatividade da energia nativa original, não a ausência de
recorrência. Esses resultados não demonstram all-order por números.

## 9. Rodas primas LSB e nova direção Schur (20/11/2026)

A propriedade original LSB_p(n)=0 ⇔ p|n produz um resultado CRT exato:
para um primo novo p não dividindo a roda anterior W, a inovação
g_p(n)=1_{p|n}−1/p é ortogonal a toda função W-periódica e tem energia
(p−1)/p²>0. Portanto, cada novo primo é uma nova direção da Gram DAS
RODAS. Câmeras compostas também podem revelar profundidades novas (4
sobre a roda 2 dá energia 1/8); “nova direção” não equivale a “novo primo”.

Os teoremas primeDepthGeometricMoment_eq_canonical e
nativeLogGenerator_basisVector_primeDepthLedger do CSA já transportam a
genealogia aritmética do ledger de câmeras primas até os momentos
nativos completados, MAS NÃO sua positividade quadrática. Continua aberto
o controle do defeito assinado do transporte roda→fonte completada.

Veja numerics/wheel_prime_schur_exact.py, evidence/wheel_prime_schur_exact.json
e reports/RELATORIO_RODAS_LSB_DIRECOES_SCHUR_20261120.md.

## 10. Câmera 2 completa, redundância C4 e dominância física (20/11/2026)

**Correção conceitual:** a câmera 4 oferece resíduo de norma² 1/8
somente quando comparada ao LSB superficial da câmera 2. Com toda
a profundidade v2, divisibilidade por 4 já está RESOLVIDA pela
câmera 2. Os teoremas Lean de C2DepthCameraRedundancy.lean formalizam
esse fato para 4 e todas as potências 2^k.

PrimeWheelNativeSignedGate.lean conecta as identidades físicas exatas
de NativeDeflation.lean com os limites Schur de ResidualTest.lean.
Os teoremas native_odd_pivot_nonneg_of_eventual_return_dominance e
native_even_pivot_nonneg_of_eventual_return_dominance demonstram o
seguinte GATE: se o retorno no verdadeiro resíduo crítico não excede,
eventualmente, a incidência ainda não resolvida, então o pivô
correspondente é não negativo.

**A condição de dominância ainda está aberta.** Não supomos que
a Gram das rodas seja a Gram dos momentos nem trocamos a fonte
por um portador Green refutado pelos no-go anteriores.

Arquivos novos: lean/C2DepthCameraRedundancy.lean,
lean/PrimeWheelNativeSignedGate.lean, lean/AuditPrimeWheelNativeSignedGate.lean,
validate-wheel-vm.sh, numerics/wheel_depth_redundancy_exact.py,
evidence/wheel_depth_redundancy_exact.json e
reports/RELATORIO_CAMERA2_PROFUNDIDADE_RETORNO_ASSINADO_20261120.md.

## 11. Mangoldt, pernas/centro e retorno não anulado (20/11/2026)

A profundidade posicional da câmera prima é o ledger do log n; a
convolução multiplicativa de Möbius extrai a função Λ nas potências
primas. Novos teoremas compilados em Lean ligam os dois diretamente
no objeto primeDepthLogLedger do CSA, antes da síntese analítica.

- PrimeDepthMangoldtBracket.lean: log n = soma Λ(d) por divisores, e
  para todo centro c≥2, Δ₁ log c <0 — embora os termos das pernas do
  stencil venham com sinal +1. Assim, centro/perna não produz sozinho
  energia positiva na derivada logarítmica. Perfil 1/n tem sinal oposto.
- PrimePowerLegCenterIncidence.lean: um divisor d≥3 numa perna do C2
  tem coeficiente +1; quando cai no centro (d≥2), coeficiente −2.
- NativeReturnPrimitiveVariation.lean: o canal de retorno deflacionado
  é exatamente a síntese nativa original ponderada por Q(zᵢ)−Q(z₀).
- NativeReturnNontrivialDerivative.lean: usando a derivada COMPLETADA
  Q′(0)=−4i h₀ com h₀>0, demonstra
  (k+1)(Q(zₖ,₁)−Q(zₖ,₀))→4h₀ e prova que o nativeOut da segunda
  fonte radial não zera para k suficientemente grande.

Consequência nova: o retorno físico não cancela exclusivamente
as contribuições que a primeira cabeça já capturou; ele também atua
na SEGUNDA direção radial original. Isso NÃO demonstra um pivô
negativo e e₁ radial não é sinônimo de nova câmera prima.

- Auditoria Lean AuditPrimeDepthMangoldtReturn.lean imprimiu apenas
  axiomas-padrão; teste intervalar Arb em numerics/mangoldt_leg_center_arb_canaries.py.
- Reproduzir: validate-mangoldt-return-vm.sh.
- Relatório: reports/RELATORIO_C2_MANGOLDT_NORMA_MEIO_RETORNO_PRIMITIVO_20261120.md.

A lei de meio (b^-k massa → b^-k/2 amplitude) já está provada
independentemente em FoundationalHalfScalingCapstone.lean.
Não misturar essa compatibilidade de norma com a hipótese ainda
aberta de PSD do COMPLETED native moment Hankel.

Próxima obrigação: dominância assinada de incidência residual sobre
retorno, no verdadeiro polinômio crítico de Schur e com todas as
correções Gamma/TFVD preservadas; não impor retorno=0 na parte nova.

## 12. C2 conectado e signo do Schur (20/11/2026)

A inversão de Dirichlet do C2 odd-core satisfaz b_T*a_T=a_T log;
no par de primos ímpares distintos o coeficiente b_T(pq) é
log(pq)*(a_T(pq)-a_T(p)*a_T(q)). Esta relação já estava provada
no primos; os novos teoremas da pesquisa investigam sua assinatura.

**Torre diádica exata** T_k=60*2^k: o conectado C2 em 3*5 é
-3/8*2^-k-1/32*4^-k<0, provado em Lean. Isso também implica
b_(T_k)(15)<0 e sinal negativo da célula TFVD/Dirichlet ORIGINAL
no parâmetro s=0 em toda a torre.

**No-go de Gram ingênua:** K_T(p,q)=a_T(p)*a_T(q)-a_T(pq),
com entradas positivas, tem determinante 2x2 [3,5] igual a
-1/64*4^-k<0 para TODO k da torre. Normalizar pela energia
quadrática da profundidade multiplicando K por 2^k produz um
resíduo escalar 3/8+1/32*2^-k>0 mas conserva determinante
-1/64<0: escala meio NÃO cria positividade. Uma correção
rank-one só à última diagonal desta matriz TENTATIVA precisaria
de delta>=1/(16+2^-k), como provado em Lean. Este não é um
orçamento afirmado para a Gamma real.

A lei de duplicação em m e a submultiplicatividade a_T(pq)<=a_T(p)a_T(q)
para TODOS os cutoffs foram apenas testadas em caixas finitas; existe
um gate abstrato Lean sob hipóteses antítonas e de duplicação,
mas tais premissas não foram provadas em geral para a massa nativa.

Os resultados C2 são finitos/aritméticos: não identificam K_T
com a Gram de F=A*N, nem demonstram PSD, Green positivo,
positividade all-order dos pivôs ou RH.

Veja reports/RELATORIO_DEFECTO_CONECTADO_C2_NORMALIZACAO_SCHUR_20261120.md,
lean/C2DepthRankOneRepairGate.lean, lean/AuditC2ConnectedDepthScale.lean,
numerics/c2_connected_depth_scale_exact.py, evidence/c2_connected_depth_scale_exact.json
e validate-c2-connected-depth-scale-vm.sh.

## 13. Levent Alpöge/Claude RH/GRH formalizada: auditoria, sinal e interface nativa (21/11/2026)

Investigação dos enunciados e cadeia de imports da prova Lean publicada em 20/11/2026 (17,4 milhões de linhas), com verificação independente MIT por kernels. Eixo lógico:
- prova externa: Main.riemannHypothesis : Mathlib.RiemannHypothesis, via rhOfAll, UpperTheory.FinalTheorems.everyCharacter, automorfia/theta lifts;
- geometria ORIGINAL CSA: NativeScalarGenuineIdentification -> NativeScalarZetaIdentification -> F(z)=A(z)N(z), sem alterar origem do operador;
- novo teorema Lean CONDICIONAL no CSA v4.32: completedNative_zero_height_real_of_RiemannHypothesis. RH da Mathlib + F(z)=0 em altura da faixa crítica implica Im(z)=0. Compilação -DwarningAsError=true aprovada, auditoria de axiomas somente propext, Classical.choice, Quot.sound.

NÃO importamos o projeto externo (Lean/Mathlib v4.33.1) na nossa branch 4.32. O teorema tem RH EXPLICITAMENTE como argumento; não é uma prova independente de RH nem de PSD do momento Hankel.

Em seu esboço, Alpöge cita sinal de uma forma Weil via determinantes e variância, Guinand–Weil / von Mangoldt, controle do resto por Parseval, multiplicidades obtidas por theta lifts com comprimento ~sqrt(X), normas/slope de Bost, trace formula. Inspecionamos partes do código (arquivos de Main, MainTheorems, MainConclusion, MeanPositiveSemidefinite, BehrendVariance e lifts). Não foi identificada equivalência física entre a forma Weil externa e nosso Green/TFVD; não inventar essa equivalência.

Uma rota analítica DOWNSTREAM usando RH é F/F(0) como produto Hadamard de zeros reais ±gamma, e h_n=Σ_gamma m_gamma gamma^(-2n-2); então a energia do Hankel é Σ_gamma (m_gamma/gamma²) P(gamma^-2)²≥0. A passagem de produto INFINITO até os h_n de nossa F NÃO foi formalizada neste commit. O esqueleto finito é formalizado no projeto momentos em MomentHankelPositivity.lean; theta/cosine PSD não é o mesmo que log-derivative Hankel.

Veja: reports/RELATORIO_ALPOGE_RH_CODIGO_SINAL_NATIVO_20261121.md,
lean/ExternalRHNativeZeroLocalization.lean, lean/AuditExternalRHNativeZeroLocalization.lean.

Fontes públicas: https://alpo.ge/remark.pdf ;
https://math.mit.edu/~drew/grh/ ;
https://github.com/CocoSgt/riemann-hypothesis-lean/blob/main/src/Supplements/Kernels/MainTheorems.lean .

## 14. Positividade SEM RH: TFVD material + verdadeiro resto físico Schur, duas direções (21/11/2026)

Objetivo independente: a prova externa de RH é apenas referência metodológica. Não importar RH como hipótese nem usar produto de zeros para gerar medida positiva.

Os módulos LEAN anteriores do CSA já forneciam:
- Kernel Pick quiral Q(z) na característica COMPLETADA F=A*N.
- Matriz Pick radial = Gram(Cauchy incident)-Gram(retorno Q*Cauchy), na métrica física ORIGINAL.
- PSD Pick all-order EVENTUAL ⇒ PSD dos dois Hankel de momentos canônicos via congruência de diferenças progressivas e limites.
- Matriz da fonte ORIGINAL seis canais TFVD/Green = 1/2 da congruência positiva de amplitude aplicada ao MESMO defeito de Cauchy/retorno.
- PSD Pick 2x2 EVENTUAL incondicional, porém apoiada por desigualdades theta/cosseno (não por um teorema C2 puro).

Nesta rodada formalizamos e auditamos:
- lean/NativeTwoPointSchurSourcePositivity.lean: subtração física exata da componente de cabeça c' = c-alpha*e0 sem alterar remainingIncident nem nativeOut; positividade do verdadeiro resto Schur sob contração original; aplicação INCONDICIONAL às duas primeiras direções; primeiro pivô deslocado canônico n=0 não negativo SEM RH.
- No mesmo módulo, a redução CONDICIONAL de TODOS os restos Schur à positividade Pick original em todas as dimensões (sem inventar uma Gram substituta).
- lean/NativeTwoPointTfvdSourcePositivity.lean: PSD INCONDICIONAL da matriz POLARIZADA material original semeada TFVD/Green de seis canais em duas direções, para cutoffs admissíveis e radial k suficientemente grande.
- lean/AuditNativeTwoPointTfvdSchur.lean: nove declarações, apenas propext, Classical.choice e Quot.sound.

A condição ainda aberta da rota independente é:
  ∀ N, ∀ᶠ k atTop, ∀ c ∈ C^N,
  ||Σ_i c_i Q(z_(k,i)) φ_(k,i)|| ≤ ||Σ_i c_i φ_(k,i)||.
Ela equivale à PSD da matriz Pick COMPLETADA em TODAS as ordens e fecha as torres de momentos pelos teoremas CSA já compilados. O próximo trabalho é demonstrá-la a partir das fontes C2/Genuine/TFVD/Green e profundidades, controlando todos os cruzamentos e a Gamma. O sinal do conectado escalar de b_T isolado NÃO basta (contraexemplo 2x2 indefinido já provado).

Relatório: reports/RELATORIO_C2_TFVD_SCHUR_POSITIVIDADE_SEM_RH_20261121.md.
Validação: validate-native-two-point-tfvd-schur-vm.sh.

## 15. Auditoria das PRs da genealogia e um novo bootstrap ALL-ORDER de TFVD/Bézout (21/11/2026)

Reabertos os fontes e status das PRs indicadas em primos, GoN, CSA e momentos. O mapa completo distingue MERGED de OPEN e provas de dimensão fixa de teoremas com n arbitrário:
reports/MAPA_ALL_ORDER_PRS_TFVD_HEAD_MARGIN_20261121.md.

A descoberta operacional é que GoN #316 fornece uma lei AFIM exata do ÚNICO coeficiente novo de cada pivô (m=2n+1 ou 2n+2), enquanto GoN #70/#131 fornecem cabeça/cauda da fonte original. Compusemos esses resultados com o critério all-order de Schur do CSA em:

- lean/AllOrderTfvdHeadMarginBootstrap.lean
- lean/AuditAllOrderTfvdHeadMarginBootstrap.lean
- validate-allorder-tfvd-headmargin-vm.sh

Foi PROVADO em Lean: se em toda ordem n e paridade b existir corte M com erro epsilon>=abs(Re(literalTail M m)) e a margem J_n(b)-m*c0*Re(literalHead M m) superar m*c0*epsilon, então todos os Hankel CANÔNICOS completados de ambos os setores são PosDef para TODO n, e a energia de bordo original é estritamente positiva em toda dimensão.

A premissa HasNativeAllOrderTfvdHeadMargins é ainda ABERTA; nenhum zero espectral nem RH é assumido. Os axiomas de auditoria são apenas propext, Classical.choice e Quot.sound. O método reduz a obrigação a provar as margens geométricas de cabeça, pois o erro de cauda controlado em n fixo não basta sem um sinal estrito.

ALERTAS DE NÃO CIRCULARIDADE:
- Primos #51 tilt não autocancela, mas #52 prova que não compensação carrier+seed é EQUIVALENTE à não anulação forte off-critical; não usar como premissa nova.
- GoN #331–333 (OPEN) fornecem positividade C2 até ordem seis baseada em certificado H6/K6; não promovê-la a todas as ordens.
- CSA #126 Green integral positivo exige prefixo aumentado PosDef; é readout, não fonte do sinal.
- CSA #124 dá também uma rota ALL-ORDER condicional por orçamento aditivo de retorno físico; Primos #34 fornece Bessel material, mas ainda falta entrelaçador exato Bessel -> Jordan/Schur completado.
- Os momentos theta/cosseno positivos não podem ser confundidos com os momentos da log derivada de F=A*N.

## 16. CAUDA EXATA: conservação dos quatro cruzamentos = Schur = theta-Green (21/11/2026)

Corrigimos explicitamente a distinção: literalTail é CAUDA ORIGINAL COMPLETA e EXATA em todo cutoff, com completion e fronteira; somente a escolha de truncar a cabeça sem ela gera erro de APROXIMAÇÃO. A identidade all-order não usa esse erro.

As igualdades já existentes no GoN e CSA foram COMPOSTAS em Lean com dois resultados novos:

- NativeExactTailSchurThetaGreenConservation.lean: para a direção crítica original de Schur (prefixo antigo invertível), todo par de cutoffs M,P tem HH+HT+TH+TT = c0*R(s,n) = c0*(massPos-massNeg) = c0*integral theta-Green. Alterar HH por cutoff muda os outros três termos na quantidade oposta EXATAMENTE. Nenhum sinal é presumido.
- NativeExactTailAllJetSignedMassGate.lean: a mesma identidade para TODA ordem N e TODO vetor x, independentemente de prefixo invertível. A forma quadrática do Hankel completado é literalmente a soma dos quatro cruzamentos C2/Genuine/TFVD e igual à massa theta assinada. Formalizada a equivalência:
  TODOS os Hankel PSD ↔ TODOS os quatro-cruzamentos completos não negativos ↔ massa negativa theta ≤ massa positiva theta em todas as direções.
  É equivalência, NÃO um certificado incondicional da desigualdade.

O novo NativeExactTailSignNoGo.lean constrói a série FORMAL de teste C(u)=1+u, H=T=C/2 não nulos, decomposição exata, primeiro Bézout par = -1. Mostra que exatidão ALGÉBRICA da cauda não fixa o sinal; NÃO representa o C2 verdadeiro. Além disso, a massa negativa theta no Schur ímpar é rigorosamente >0 em TODA ordem na fonte real.

Relatório detalhado: reports/RELATORIO_TFVD_CAUDA_EXATA_SCHUR_ALL_ORDER_SINAL_20261121.md.
Auditoria: lean/AuditNativeExactTailAllOrder.lean (20 declarações, axiomas apenas propext, Classical.choice, Quot.sound).
Validação: validate-native-exact-tail-allorder-vm.sh (Lean -DwarningAsError=true). Nenhuma hipótese RH.

**Próxima obrigação geométrica:** encontrar uma LEI DE COMPENSAÇÃO ASSINADA, preferivelmente via entrelaçador Bessel Primos #34 → retorno quiral F=A*N, que prove a massa positiva domina a negativa em TODOS os polinômios de jets da fonte nativa, não apenas certificados de ordem finita. A conservação da cauda já está FECHADA; a dominação não.

## 17. Limite sigma→1/2 e deslocamento da primeira inversão de sinal (21/11/2026)

Reaberto o estudo ORIGINAL momentos/investigations/c2_sigma_crossing_even_jet_hierarchy_20261105:
d=0.2 gera primeira janela 2x2 negativa no SHIFT s=7; d=1e-5 no SHIFT s=32; extrações de jets usam a cabeça C2+cauda Hurwitz EXATA. Esse deslocamento da PRIMEIRA JANELA é NUMÉRICO, não prova de limite all-order ou de primeira dimensão negativa.

Há uma ponte importante REAL em GoN:
SigmaNeighborhood.sigma_matrix_continuous_center prova que para toda dimensão N fixa a matriz de jets sigmaMatrix(d,s,N) varia continuamente em d=0, e sigma_matrix_center a identifica com os momentos canônicos completados.

Nesta rodada formalizamos SigmaNativeFullFailureDimensionEscapes, a hipótese precisa de que a primeira dimensão NEGATIVA da matriz Hankel COMPLETA (não o índice da janela 2x2) vai a infinito quando d→0: ∀b,N ∃δ>0 ∀0<|d|<δ, sigmaMatrix(d,s_b,N).PosSemidef.

Sob essa hipótese AINDA ABERTA, três novos teoremas compilados demonstram:
- todos Hankel originais no centro são PSD;
- a forma EXATA TFVD de quatro cruzamentos HH+HT+TH+TT é não negativa para todos M,P, b,N,x;
- a massa theta positiva da fonte completada domina a negativa para todos os jets.
Não se assume RH, e não se presume que a hipótese de fuga tenha sido demonstrada.

**NO-GO rigoroso:** uma sequência artificial com h0=1,h1=1,h2=2,h3=5,h4=63/5 e cauda h_n=(63/5)*3^(n-4) tem TODOS os menores consecutivos 2x2 não negativos, mas determinante de Hankel 3x3 = -2/5. Portanto, mesmo provar que a primeira JANELA negativa foge para infinito não é suficiente para positividade all-order.

Lean e auditoria (7 declarações, axiomas-padrão somente):
- lean/TransverseSignThresholdCenterClosure.lean
- lean/NativeSigmaFirstFailureAllOrderGate.lean
- lean/TransverseTwoWindowNotEnough.lean
- lean/AuditNativeSigmaThresholdCenterClosure.lean
- validate-sigma-first-failure-center-vm.sh
Relatório: reports/RELATORIO_SIGMA_FUGA_PRIMEIRA_NEGATIVIDADE_ALL_ORDER_20261121.md

**Próxima obrigação:** controlar em toda dimensão a PRIMEIRA falha de PSD da matriz inteira, ou demonstrar diretamente a dominância incidente-retorno física all-order pela geometria C2. A mera fuga dos menores adjacentes D_s é uma indicação útil da curvatura transversal mas não entrega Schur global.
