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
