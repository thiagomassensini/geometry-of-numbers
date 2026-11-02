# Fonte C3 acelerada: certificação finita da direção crítica de dimensão três

**Resultado: PASS finito com caixas theta; PARTIAL para o mecanismo geométrico geral.** O Lean certificou, nos setores par e ímpar, o pareamento completo, uma margem para a cabeça C3 e a positividade dos respectivos residuais de Schur. As ordens aqui consideradas já eram cobertas por outros resultados finitos: o avanço é a cadeia explícita que conserva o orçamento da fonte. O sinal é obtido das caixas theta dos coeficientes/momentos; não se demonstrou uma lei geométrica de sinal independente de theta, nem positividade em toda ordem.

## A — Base e proveniência

Base: commit `da8a1fb92a7e4dc64110ffefbb4dee5a2aa4a874` da branch da PR #143. Esta branch é empilhada sobre ela. Não modifica a PR nem substitui seus objetos. A edição não commitada preexistente na worktree da #143 foi preservada. O arquivo `C3MultiplicativeSecondEven.lean` que integra a base é um esqueleto independente, não utilizado pelos novos módulos.

A PR #41 fornece a direção e o residual de Schur, sem exigir seu sinal. A PR #70 fornece a fonte C3 original acelerada e sua cauda para cutoff arbitrário. A #143 fornece a repartição polarizada `HH + HT + TH + TT` e o orçamento de erro. São mantidos os dois argumentos, cruzamentos, pernas e bordo; a parte real é tomada depois da composição. A norma dos coeficientes usada na estimativa não substitui a métrica física.

Os novos resultados também utilizam `material_theta_integral_input` e as caixas de `IntegralCertificate.lean`. Essa dependência efetiva da representação theta da mesma fonte fornece, entre outras coisas, a **margem de sinal do pareamento completo**. A demonstração numérica em Lean não usa como hipótese a positividade do pivô; porém, a margem certificada para o pareamento completo já implica esse sinal pela identidade algébrica. Portanto, transportar essa margem para a cabeça e voltar ao pivô não constitui uma explicação geométrica independente de sua positividade.

## B — Resultados novos verificados pelo Lean

`C3Tail256.lean` identifica a cauda como o jet da cauda C3 acelerada original e prova para todo `M>0` e `k`

\[
 \|T_{M,k}\|\leq \frac{96\,14!}{729(3M-1)^{13}}\,4^{2k}.
\]

Em `M=256`, para `k≤6`, cada cauda é no máximo `10⁻²⁰`; a cabeça correspondente tem norma no máximo 1. A caixa C3 preexistente limita o coeficiente de ordem zero; uma estimativa theta limita os demais coeficientes em módulo.

`C3Budget256.lean` prova, para ambos os setores e quaisquer dois vetores de dimensão três com massa de coordenadas no máximo 2,

\[
 \lvert B(x,y)-HH_{256}(x,y)\rvert\leq 3\cdot10^{-18}.
\]

O núcleo completo e os três termos de cauda aparecem no lado controlado. A estimativa também vale para argumentos distintos, não apenas na diagonal.

`CriticalCoordinates.lean` fornece fórmulas exatas para o vetor crítico e a direção mônica original, exigindo apenas inversibilidade do prefixo antigo. `CriticalBoxes.lean` certifica essa inversibilidade e `‖z_s‖₁≤2` nos dois setores usando as caixas theta. `C3Critical256.lean` combina esses resultados sem hipóteses adicionais:

\[
 \left|c_0^2p_{s,2}-\operatorname{Re}HH_{256}(z_s,z_s)\right|
 \leq 3\cdot10^{-18},\qquad s\in\{0,1\}.
\]

`PivotBoxes.lean` avalia com intervalos racionais verificados pelo kernel a expressão algébrica completa, obtendo as seguintes conclusões para cada setor:

\[
 B(z_s,z_s)>6\cdot10^{-18},\qquad
 \operatorname{Re}HH_{256}(z_s,z_s)>3\cdot10^{-18},\qquad
 p_{s,2}>0.
\]

Os teoremas são `sourcePair_gt_six`, `sourceHead_gt_three` e `pivot_positive_from_certified_boxes`. O primeiro usa as caixas theta e uma expressão da direção que é algebricamente identificada ao residual de Schur; o segundo subtrai a cota de cauda comprovada, e o terceiro aplica o transporte da #41. A prova não recebe o sinal como hipótese nem invoca os certificados de positividade explicitamente bloqueados na auditoria. A ordem lógica da prova é informativa: **theta → sinal do pareamento completo → sinal da cabeça → pivô**, e não cabeça geométrica → sinal independente.

## C — Diagnósticos e limites

`diagnose_c3_256.py` usa os 16 momentos decimais previamente publicados, 70 dígitos de trabalho e a característica completada; não recebe zeros ou alturas. As cabeças observadas são aproximadamente `2,7546034·10⁻¹⁴` no par e `1,9972418·10⁻¹⁷` no ímpar. Essas aproximações são diagnósticos, não são usadas para provar as desigualdades Lean. Hashes e saída constam em `evidence/`.

`interval_probe.py` testa em Python racional o pareamento completo com caixas impressas por `InspectBoxes.lean`, incluindo os cruzamentos algébricos. O diagnóstico indicou intervalos aproximadamente `[2,7546032373·10⁻¹⁴, 2,7546035826·10⁻¹⁴]` no par e `[1,9972326725·10⁻¹⁷, 1,9972508516·10⁻¹⁷]` no ímpar. O programa é independente da prova Lean e a saída decimal é arredondada; o certificado Lean efetivo é `sourcePair_gt_six`, obtido pela expressão algébrica dos mesmos dados e pelas caixas verificadas no kernel.

A cota `3·10⁻¹⁸` é absoluta e específica à dimensão três e cutoff 256. Ela não é uma cota relativa uniforme nos pivôs e não implica sinal all-order. Não se identificou o sinal do Green completo com o da cauda nem com a positividade de uma Gram auxiliar.

## D — Próxima obrigação mínima

O resultado finito deixa um alvo mais forte e não circular quanto à **origem geométrica**: demonstrar diretamente da cabeça C3 e de suas relações originais uma margem `Re HH₍₂₅₆₎(zₛ,zₛ)>3·10⁻¹⁸`, sem obter antes o sinal do pareamento completo através das caixas theta. É preciso reter os dois argumentos, as duas pernas, o retorno, a borda e os cruzamentos. Depois, procurar uma versão dependente da ordem e setor que controle conjuntamente margem, tamanho da direção e HT/TH/TT. A prova atual não fornece essa lei.

## E — Validação e reprodução

No host `llm`, da raiz desta worktree e com os caches de dependências indicados em `compile.sh`:

```bash
bash research/c3-dimension-three/validate.sh
lake build --wfail
bash scripts/audit-foundation.sh
bash scripts/audit-geometry.sh
bash scripts/audit-analysis.sh
/home/thlinux/miniforge3/bin/python research/c3-dimension-three/diagnose_c3_256.py
python3 research/c3-dimension-three/interval_probe.py
```

Os módulos novos são compilados individualmente com `-DwarningAsError=true`; `#print axioms` registra apenas `propext`, `Classical.choice`, `Quot.sound`. A auditoria transitiva em `C3Audit.lean` examina tipos e corpos, exige cauda original, caixas theta, vetor crítico e repartição, e bloqueia a lista explícita de teoremas de sinal. Isso não é uma busca semântica por toda prova matematicamente equivalente.

`lake build --wfail` e as três auditorias passaram. Os logs estão em `evidence/`. Os `.olean` das dependências anteriores foram reutilizados; não foi realizada reconstrução limpa de todos os repositórios dependentes. Não foram introduzidos `sorry`, `admit`, `native_decide` ou axiomas.
