# Residual de Schur na fonte Bézout e na decomposição TFVD literal

**Classificação: PARTIAL.** O transporte algébrico e o controle da cauda estão demonstrados em toda ordem finita. O teste de sinal do ledger com o bordo C3 original está agora certificado em Lean para a segunda direção par, com uma margem quantitativa e sem hipótese de positividade Hankel. A lei de sinal para toda ordem e uma Gram física positiva completa continuam abertas.

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

O lema `native_residual_pos_of_literal_margin` é uma regra suficiente de verificação: um valor finito de `HH.re` acima do orçamento provado implica sinal positivo. A regra genérica não é anunciada como uma margem incondicional em toda ordem. A instância finita efetivamente descarregada está descrita abaixo.

### 5. Reorganização exata do bordo

[Repartition.lean](Repartition.lean) prova que mover um bordo `U` da cauda para a cabeça em um argumento, e `V` no outro, preserva exatamente os quatro termos somados. O lema `native_residual_repartition` mantém o mesmo residual nativo e o mesmo vetor `z`. A instanciação com o bordo específico C3 da PR #69 foi concluída em [NativeRepartition64.lean](NativeRepartition64.lean). `originalBoundaryJet` usa diretamente o `c3Boundary` e o multiplicador completado originais. Os teoremas `regrouped_head64_jet`, `regrouped_tail64_jet` identificam exatamente as parcelas com `completedHead64` e `completedTailError` preexistentes; `regrouped_source` prova a recomposição da mesma fonte em todo índice.


### 6. Propriedade independente da fonte, com margem efetivamente provada

[TwoEvenSourceMargin.lean](TwoEvenSourceMargin.lean) prova uma estimativa explícita, sem momentos, pivôs, inversas ou whitening nas hipóteses: quatro coeficientes de `H` dentro de `2·10⁻¹²` dos centros racionais originais e quatro coeficientes de `T` de norma no máximo `10⁻¹⁵` implicam, para **toda** direção mônica `z=(t,1)` com `|t|≤1`,

\[
\Re HH(z,z)>10^{-8},\qquad
E(z,z)\le10^{-13}.
\]

O primeiro limite é obtido por uma desigualdade racional exata para o polinômio quadrático de referência, seguida de um limite bilinear do erro de seus coeficientes. O segundo inclui separadamente HT, TH e TT. Esses centros são testemunhas de inclusão; não definem outra fonte. Não há hipótese de positividade disfarçada no lugar das inclusões já provadas.

[NativeRepartition64.lean](NativeRepartition64.lean) descarrega essas inclusões na fonte original, reutilizando **`canonical_four_source_boxes`** e **`completed_tail_jet_error`** da PR #69. Não recalcula as quatro caixas. As duas conclusões são `native_regrouped64_head_lower` e `native_regrouped64_error_upper`.

Portanto, `native_regrouped64_total_lower` prova a propriedade quantitativa da própria fonte:

\[
\Re(HH+HT+TH+TT)(z,z)>10^{-8}-10^{-13}
\]

em toda a faixa `|t|≤1`. O enunciado não contém momentos, pivôs ou inversas.

Em seguida, prova-se que o vetor crítico **verdadeiro**, com a normalização mônica já transportada, é

\[
z=\left(-\frac{2c_2}{c_1},1\right),\qquad
\left|\frac{2c_2}{c_1}\right|\le1.
\]

As caixas da fonte garantem `c₁<−1/100`, `|c₂|≤1/1000` e `c₀>0`. A recorrência original descarrega a inversibilidade do prefixo 1×1, sem recorrer a um teorema anterior de positividade de momentos. Nomes: `native_monic_two_direction`, `native_monic_two_coordinate_bound`, `native_even_one_isUnit_from_source`.

A substituição desse mesmo vetor nos quatro termos fornece finalmente:

\[
\boxed{c_0\,\mathrm{nativeSourceSchurRemainder}(0,1)>10^{-8}-10^{-13}>0.}
\]

Teoremas finais: `native_second_even_balance_lower_from_original_split`, `native_second_even_remainder_pos_from_original_split`, `native_second_even_pivot_pos_from_original_split`.

É um novo fechamento da **rota de prova pela fonte e pelo ledger literal** para um pivô que já era conhecido por outras rotas. Não se anuncia uma nova ordem de positividade, nem se extrapola essa margem para outros pivôs.

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

A soma reproduz o alvo diagnóstico. A margem passa numericamente após a reorganização exata; os pesos não foram ajustados ao sinal. **Os números desta tabela continuam sendo diagnósticos**, com erro devido também ao arredondamento das referências. A margem foi certificada independentemente pela estimativa racional conservadora da seção B.6, aplicada ao vetor verdadeiro; não pela validação destes números de ponto flutuante.

## D — O que permanece aberto

1. Derivar uma orientação de sinal da fonte para direções críticas de ordem arbitrária. A convergência do orçamento para cada ordem fixa não fornece essa orientação.
2. Obter margens críticas relativas que permaneçam controláveis quando a ordem aumenta. A estimativa `C·16ⁿ/(M+1)` não é coercividade uniforme.
3. Identificar uma Gram positiva física completa com este kernel, se tal identificação existir. Não foi demonstrada uma isometria desse tipo.

Não foram provados positividade Hankel all-order, contratividade física all-order, positividade de todos os resíduos ou construção incondicional do operador infinito de alturas. Os resultados finitos anteriores são preservados. O teste `s=0,n=1,M=64`, antes numérico, está agora concluído formalmente.

## E — Próximo passo mínimo e reprodução

O encaixe mínimo com a PR #41 e o teste da margem original estão fechados. A continuação all-order precisa de uma propriedade adicional da síntese TFVD que produza um limite inferior independente para a parte finita e um controle relativo dos três termos restantes, na direção crítica variável. A relação `E→0`, sozinha, não fornece esse limite inferior.

A obrigação concreta é obter tal controle da fonte antes de usar o sinal do pivô. Postular `∃M, HH.re>E` para cada ordem apenas transfere a obrigação: pela convergência já demonstrada, essa existência pode ser deduzida da própria positividade que estaria em questão. A certificação presente evita essa circularidade porque suas inclusões e seus limites racionais foram demonstrados separadamente, para a fonte original e para uma faixa inteira de direções.

Não é preciso recalcular as quatro caixas nem aumentar cutoffs às cegas. O próximo avanço estrutural deve explicar como produzir a margem quando a ordem varia; a lei de sinal geral permanece uma obrigação matemática real.

No host `llm`, a partir da raiz do repositório:

```bash
python3 research/tfvd-bezout-schur-residual/validate.py
```

O script compila explicitamente os módulos novos com `-DwarningAsError=true`, imprime os axiomas de todas as declarações públicas e audita transitivamente tipos e corpos. Executa também `lake build --wfail`, builds focados, auditorias Foundation/Geometry/Analysis e a regressão de doze fontes. Os módulos de pesquisa são compilados pelo script; o build da raiz, sozinho, não os cobre.

As provas algébricas e os majorantes genéricos usam o `lake env` mínimo do operador original, acrescido do cache desta pesquisa. A integração `NativeRepartition64`, a regressão e a auditoria usam `compile_certified_module.sh`, que carrega os certificados já compilados da PR #69 no ambiente histórico correspondente. Não há novo pin ou alteração das dependências. O carregador legado fica restrito aos módulos que consomem o certificado histórico da PR #69; os demais continuam no ambiente mínimo. O diagnóstico Python usa `/home/thlinux/miniforge3/bin/python`; pode-se especificar `CARRY_DIAGNOSTIC_PYTHON` para outro interpretador que já tenha `mpmath`.

Validação executada: **28 checks passaram**, incluindo **217 declarações públicas auditadas** (166 teoremas e 51 definições/abreviações). Os únicos axiomas encontrados foram `propext`, `Classical.choice` e `Quot.sound`. A auditoria transitiva rejeita dependências dos certificados posteriores de positividade enumerados no código. Na integração `NativeRepartition64`, rejeita também a calibração theta de `c₀≥1/3`: a positividade de `c₀` nessa prova é deduzida das próprias caixas C3. O maior RSS medido foi **8,25 GiB**, registrado por módulo em `evidence/checks.json`; a importação conjunta dos certificados cabe na RAM atual da VM.

Os arquivos `evidence/checks.json`, `evidence/kernel-Audit.log`, `public-roots.json` e `evidence/source-sha256.json` registram comandos, resultados, inventário e hashes. O modo `--resume` reaproveita apenas compilações bem-sucedidas cujas fontes e dependências locais diretas continuam anteriores ao artefato compilado; regenera e executa novamente a auditoria.

A fonte, pesos, amplitudes, fases, métrica, completion, pins, `main`, PR #69 e os dois módulos não rastreados preexistentes do operador permanecem preservados. O swap temporário usado durante o diagnóstico de importações foi desativado e removido; nenhuma configuração persistente da VM foi alterada.

**Fecho:** o residual da PR #41 tem transporte monicamente correto ao Schur da fonte e um ledger TFVD literal com erro convergente, em toda ordem finita. A margem reorganizada na segunda direção par foi certificada a partir da fonte original, sem hipótese de positividade Hankel. A orientação de sinal geral continua aberta.
