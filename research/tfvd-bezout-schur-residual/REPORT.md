# Residual de Schur na fonte Bézout e na decomposição TFVD literal

**Classificação: PARTIAL.** O transporte algébrico e o controle da cauda foram demonstrados em toda ordem finita. A margem positiva no ledger com o bordo C3 reorganizado foi apenas testada numericamente; sua certificação específica e uma lei de sinal para toda ordem permanecem abertas.

Repositório: `thiagomassensini/geometry-of-numbers`. Branch: `agent/tfvd-bezout-schur-residual`. Base: `a236b218f3e68a8fbf714902de196f7234faeaf3`, da PR #69, preservada e não mesclada automaticamente. Operador consultado sem alterações: `bfeb10fd2425400fa38139903d12bf0599f02e53`. Não foram criadas worktrees.

## A — O que já estava demonstrado

A lógica da PR #41 separa a ortogonalização algébrica do sinal dos pivôs. Reutilizamos as definições originais `sourceMomentMatrix`, `sourceMomentCoupling`, `sourceMomentSchur` e o resto `nativeSourceSchurRemainder`, do módulo `NativeSourceAllOrderSchur` do operador. A hipótese de prefixo neste trabalho é **IsUnit**, não `PosDef`.

A recorrência original `canonicalCompletedNativeLogDerivativeMoment_real_recurrence` relaciona os coeficientes da característica completada e os momentos canônicos. `nativeSourceSchurRemainder_eq` já identifica o resto nativo como `c₀ p`. Não se pode identificá-lo nominalmente com um pivô mônico em outras coordenadas.

A síntese TFVD original dispõe de `canonicalC3BracketTfvdCompletionState`, `canonicalC3BracketTfvdCompletedTracePair` e `canonicalC3BracketTfvdCompletedTracePair_eq_F_negFprime`. Eles conservam os canais de valor e log-jet, retorno de cauda, fator Xi, chart C3, fase material e companion de bordo.

A PR #69 já certificou quatro caixas da mesma fonte C3. Elas não foram recalculadas nem utilizadas como hipóteses escondidas nas novas identidades. Os resultados de positividade finita posteriores também não são dependências das provas novas.

## B — O que foi demonstrado agora

### 1. Kernel da fonte antes dos momentos

Em [SourceBezout.lean](SourceBezout.lean), escrevemos `C(u)=Σ cₙuⁿ`, `A₀=-uC'`, `A₁=-C'`. O kernel formal tem numerador

\[
(u-v)\mathscr B_s(u,v)=A_s(u)C(v)-A_s(v)C(u).
\]

Ele é definido pelos coeficientes das duas fontes, usando uma diferença dividida formal; não há divisão singular na diagonal e não se constrói `1/C` para defini-lo. A recorrência `CR=-C'` implica, em qualquer dimensão finita,

\[
B_{s,r}=T_r H_{s,r}T_r^T,\qquad
(T_r)_{ij}=\mathbf1_{j\le i}c_{i-j}.
\]

Teoremas: `source_bezout_to_hankel_congruence`, `source_bezout_det`; aplicação à sequência original: `native_source_bezout_congruence`, em [SourceNative.lean](SourceNative.lean). Os setores `false` e `true` são respectivamente a Hankel original e a deslocada. As equivalências de positividade por congruência são equivalências, não provas incondicionais de seus lados.

### 2. Mesma direção crítica; fatores c₀ e c₀² separados

Se o prefixo antigo é invertível, sejam

\[
v=(-H_{s,n}^{-1}b,1),\quad T_{n+1}^Ty=v,\quad z=c_0y.
\]

[SchurTransport.lean](SchurTransport.lean) prova:

\[
y^TB_{s,n+1}y=p,\qquad z_{n}=1,\qquad
z^TB_{s,n+1}z=c_0^2p.
\]

Para **todo** vetor real independente `x`, a identidade mais forte é

\[
x^TB_{s,n+1}z=x_n c_0^2p.
\]

Ela inclui todos os cruzamentos e demonstra a estacionariedade contra cada direção antiga. Nomes: `sourceDirection_transport`, `sourceDirection_energy`, `monicSourceDirection_energy`, `monicSourceDirection_pair`.

[SourceSchur.lean](SourceSchur.lean) define também o Schur ordinário do próprio bloco da fonte:

\[
p_B=B_{nn}-d^TB_{s,n}^{-1}d.
\]

Prova-se que o prefixo da fonte é invertível, que `z` coincide com sua direção crítica construída **somente dos coeficientes da fonte**, e que

\[
p_B=c_0^2p=c_0\,\mathrm{nativeSourceSchurRemainder}.
\]

Teoremas: `source_prefix_isUnit`, `monicSourceDirection_eq_sourceCritical`, `sourceSchur_eq_scaled`, `native_sourceSchur_remainder`. Assim, a identidade não fica restrita a dar outro nome à energia de um vetor transportado: ela identifica o complemento de Schur calculado diretamente no bloco da fonte.

### 3. Substituição na TFVD completada literal

[LiteralNativeTrace.lean](LiteralNativeTrace.lean) expõe apenas as projeções e a regularidade necessárias do estado TFVD já existente. As fórmulas são as mesmas do traço de PR #67; `stateTrace_head_tail` e `completedTrace_head_tail` provam sua igualdade com o traço original antes dos jets. Isso evita importar consumidores posteriores de Jacobi, sem reconstruir a fonte ou alterar seu carrier.

Depois dessa igualdade de pares completos, definimos

\[
H_M(n)=\operatorname{jet}_{2n}(\mathrm{headTrace}_M.1),\quad
T_M(n)=\operatorname{jet}_{2n}(\mathrm{tailTrace}_M.1).
\]

O teorema `literal_head_tail` prova `C=H_M+T_M`. As parcelas permanecem complexas. Não se presume que um prefixo finito seja par ou tenha coeficientes reais.

[LiteralCompanion.lean](LiteralCompanion.lean) prova, separadamente para cabeça e cauda, que o segundo canal retido é exatamente menos a derivada do primeiro, com Xi, chart, fase `I` e companion de bordo originais. [CompanionJets.lean](CompanionJets.lean) transporta essa identidade para os coeficientes usados no kernel, com o fator exato

\[
\operatorname{coeff}_n(-C'_H)
=\tfrac12\operatorname{jet}_{2n+1}(\mathrm{headTrace}_M.2),
\]

e analogamente para a cauda. O setor par acrescenta o deslocamento por `u`. Teoremas: `literal_head_response_odd`, `literal_tail_response_odd`, `literal_head_response_even_succ`, `literal_tail_response_even_succ`. Não se descarta o companion nem se substitui sua normalização.

[LiteralTfvd.lean](LiteralTfvd.lean) prova a decomposição bilinear em **dois argumentos reais independentes e dois cutoffs independentes**:

\[
x^TB_{s,r}y=HH+HT+TH+TT.
\]

Em seguida, substitui exatamente a mesma direção `z` nos quatro termos:

\[
HH(z,z)+HT(z,z)+TH(z,z)+TT(z,z)
=c_0\,\mathrm{nativeSourceSchurRemainder}(s,n).
\]

Teoremas: `literal_four_terms`, `native_residual_literal_four_terms`. A parte real não é aplicada separadamente às parcelas antes dessa identidade.

**Alcance:** `complexPair` é um pareamento bilinear complexo de coeficientes, aplicado aos casts de vetores reais. Não é um produto hermitiano positivo nem uma isometria física. Nenhum teorema novo identifica automaticamente este kernel com uma Gram de Hilbert ou com a métrica Cauchy do carrier. A congruência e a proveniência do traço são o que foi provado.

### 4. Propriedade independente da fonte: erro TFVD tende a zero

[LiteralTailBounds.lean](LiteralTailBounds.lean) deriva do majorante original do bracket, para `‖w‖≤1/2`,

\[
\|\mathrm{cell}_m(w)\|\le\frac4{(m+1)^2},\qquad
\|\mathrm{tail}_M(w)\|\le\frac8{M+1}.
\]

A continuidade do **mesmo** multiplicador Xi/chart no disco compacto de raio `1/4`, seguida pela desigualdade de Cauchy, fornece

\[
\exists C>0,\ \forall M,n,\quad
\|T_M(n)\|\le\frac{C\,16^n}{M+1}.
\]

`C` é derivado da fonte original; não é métrica, normalização nem parâmetro escolhido para fabricar um sinal. O teorema é de existência; não entrega uma constante racional concreta.

[KernelBudget.lean](KernelBudget.lean) mantém a fórmula de cada coeficiente misto e soma os módulos de todos os termos, obtendo um orçamento explícito `E` para `HT+TH+TT`:

\[
|x^TB_{s,r}y-HH(x,y)|\le E_{M,P}(x,y).
\]

[LiteralBudgetLimit.lean](LiteralBudgetLimit.lean) prova, sem hipótese de sinal ou inversibilidade,

\[
\forall r,x,y\text{ fixos},\qquad E_{M,M}(x,y)\longrightarrow0.
\]

Nomes: `literal_error_bound`, `literal_tail_jet_envelope`, `literal_error_budget_tendsto_zero`. É controle genuíno da aproximação do kernel original. **Não** é estimativa uniforme na ordem, margem relativa crítica ou positividade.

O lema `native_residual_pos_of_literal_margin` é somente uma regra suficiente de verificação: um valor finito de `HH.re` acima do orçamento provado implica sinal positivo. A desigualdade não foi declarada verdadeira para toda direção da fonte.

### 5. Reorganização exata do bordo

[Repartition.lean](Repartition.lean) prova que mover um bordo `U` da cauda para a cabeça em um argumento, e `V` no outro, preserva exatamente os quatro termos somados. O lema `native_residual_repartition` mantém o mesmo residual nativo e o mesmo vetor `z`. Ele vale para bordos arbitrários; sua instanciação formal com o stencil específico C3 da PR #69 é o próximo encaixe, ainda não concluído aqui.

## C — O que foi refutado ou apenas testado

`negative_control_recurrence` e `negative_control_hankel_not_posSemidef`, em [SourceBlocks.lean](SourceBlocks.lean), dão um controle exato:

\[
C(u)=1-u-u^2,\quad B_{0,2}=\begin{pmatrix}1&2\\2&-1\end{pmatrix},\quad\det B=-5.
\]

A recorrência logarítmica vale em toda ordem para esse controle. Portanto, recorrência, diferença dividida e centro não nulo, isoladamente, não obrigam o sinal. **Não é um contraexemplo à fonte Carry original.**

O script [diagnose_literal_terms.py](diagnose_literal_terms.py) usa 70 dígitos, os quatro centros de referência já certificados na PR #69 e as fórmulas originais Xi/Gamma/chart/C3. Não chama theta, zeta, zeros ou alturas. Os centros são usados como valores diagnósticos, não como intervalos certificados da fonte.

Para `s=0,n=1`, nas referências, o residual mônico vale aproximadamente `2.08499290015136e-8`. No prefixo bruto `M=64`, `HH≈1.799841e-3`, `TH≈-1.805285e-3`; há cancelamento grande. O teste suficiente de margem falhou nos oito cutoffs examinados, de 0 a 4096. **Isso não prova impossibilidade desse teste em todos os cutoffs.**

Com o bordo fixo original da PR #69 em `M=64`, cujos pesos são

```
[728,-1444,638,1092,-2445,2640,-1911,987,-363,91,-14,1]/729
```

nas doze amostras de endereços 194 a 205, o mesmo diagnóstico deu:

| Parcela | Valor aproximado |
| --- | ---: |
| HH | 2.0849929566434e-8 |
| HT | 3.7223646e-18 |
| TH | -5.6864280e-16 |
| TT | 3.4669513e-32 |
| Orçamento dos três erros | 5.9996005e-16 |

A soma reproduz o alvo diagnóstico. A margem passa numericamente após a reorganização exata; os pesos não foram ajustados ao sinal. **Esta tabela não é um certificado Lean nem um novo teorema de positividade finita.** A discrepância pequena inclui o arredondamento dos centros de referência.

## D — O que permanece aberto

1. Instanciar `native_residual_repartition` com o bordo C3 original já provado na PR #69.
2. Reutilizar suas caixas e seu majorante de cauda para certificar a margem do ledger reorganizado no **vetor crítico verdadeiro**, não no vetor dos centros arredondados.
3. Encontrar uma propriedade independente da fonte que forneça orientação de sinal para ordens arbitrárias. A convergência do orçamento e a identidade com o Schur não fornecem essa orientação.
4. Identificar uma Gram positiva física completa com este kernel, se tal identificação existir. Nada aqui prova uma isometria desse tipo.

Não foram provados positividade Hankel all-order, contratividade física all-order, positividade de todos os resíduos ou construção incondicional do operador infinito de alturas. Os resultados finitos anteriores são preservados.

## E — Próximo passo mínimo e reprodução

O alvo mais curto é a margem de `s=0,n=1,M=64` com o bordo original. Sejam `U₆₄` os jets do multiplicador completado original vezes o `c3Boundary` original, `H*=H₆₄+U₆₄`, `T*=T₆₄-U₆₄`, e `z=sourceCritical nativeC false 1`. Provar:

\[
\mathrm{directionalBudget}(H^*,T^*)+
\mathrm{directionalBudget}(T^*,H^*)+
\mathrm{directionalBudget}(T^*,T^*)
<\operatorname{Re}\,\mathrm{coefficientPair}(H^*,H^*;z,z).
\]

As caixas da PR #69 já existem: o trabalho útil é transportá-las para essa desigualdade e controlar a direção exata. Esse passo testará uma margem da síntese original, sem recalcular os quatro certificados ou usar uma positividade Hankel como entrada. Mesmo que passe, será um certificado nessa direção finita, sem extrapolação all-order.

No host `llm`, a partir da raiz do repositório:

```bash
python3 research/tfvd-bezout-schur-residual/validate.py
```

O script compila explicitamente os módulos novos com `-DwarningAsError=true`, imprime os axiomas de todas as declarações públicas e audita transitivamente tipos e corpos. Executa também `lake build --wfail`, builds focados, auditorias Foundation/Geometry/Analysis e a regressão de doze fontes. Os módulos de pesquisa são compilados pelo script; o build da raiz, sozinho, não os cobre.

O ambiente das novas provas é o `lake env` mínimo do operador original, acrescido apenas do cache desta pesquisa. Não há novo pin, alteração em dependências ou substituição da biblioteca do operador pelo checkout maior de Geometry. O diagnóstico Python usa `/home/thlinux/miniforge3/bin/python`; pode-se especificar `CARRY_DIAGNOSTIC_PYTHON` para outro interpretador que já tenha `mpmath`.

Validação executada: **26 checks passaram**, incluindo **171 declarações públicas auditadas** (127 teoremas e 44 definições/abreviações). Os únicos axiomas encontrados foram `propext`, `Classical.choice` e `Quot.sound`. A auditoria transitiva também rejeita dependências dos certificados posteriores de positividade enumerados no código. O maior RSS medido nas compilações novas foi aproximadamente **7,97 GiB**.

Os arquivos `evidence/checks.json`, `evidence/kernel-Audit.log`, `public-roots.json` e `evidence/source-sha256.json` registram comandos, resultados, inventário e hashes. O modo `--resume` reaproveita apenas compilações bem-sucedidas de fontes inalteradas; regenera e executa novamente a auditoria.

A fonte, pesos, amplitudes, fases, métrica, completion, pins, `main`, PR #69 e os dois módulos não rastreados preexistentes do operador permanecem preservados. O swap temporário usado durante o diagnóstico de importações foi desativado e removido; nenhuma configuração persistente da VM foi alterada.

**Fecho:** o residual da PR #41 agora tem transporte monicamente correto ao Schur da fonte e um ledger TFVD literal com erro convergente, em toda ordem finita. O novo teste de margem reorganizada ainda aguarda certificação; a orientação de sinal geral continua aberta.
