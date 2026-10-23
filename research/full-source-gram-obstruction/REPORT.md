# Norma do carrier completado e energia da projeção na normal

**Resultado: PARTIAL para a ponte canônica; NO-GO para as realizações especificadas abaixo.** O teste agora inclui o carrier operatório completado inteiro, com os canais archimediano e de câmera. Sua energia central excede a massa canônica. A energia da projeção ortogonal da tangente na normal, por outro lado, fica estritamente abaixo dela. Os dois defeitos foram demonstrados quantitativamente, na norma já existente.

Não foi provada impossibilidade de uma Gram da geometria completa. O carrier aqui é exatamente `CanonicalCompletedC3FullWronskianOperatorCarrier`: ele já resulta de uma projeção contínua do estado enriquecido e de um packing de canais. Não se declarou sua norma igual à norma de todos os dados materiais antes dessa projeção.

## A — O que já estava demonstrado

### Base, estado e fontes

- Repositório: `thiagomassensini/geometry-of-numbers`.
- Branch: `agent/full-source-gram-obstruction`.
- Base: `5ed5f183753410c01f9b92af5a4cfc1d6a2aec11`, PR #76, `agent/native-completed-pairing`.
- A #76 foi conferida aberta, draft e empilhada sobre a #75. Não houve merge automático.
- `origin/main`: `59e53d863f4ef0ad998b0eb19fd3891c9839cc35`.
- Operador consultado: `/home/thlinux/carry-self-adjoint-operator`, HEAD `bfeb10fd2425400fa38139903d12bf0599f02e53`.
- Compilação no host `llm`, em worktree isolada. Só novos arquivos deste diretório pertencem à mudança.

A fonte, endereços, amplitudes, fases, câmeras, métricas, Gamma, completion e pins foram preservados. O trabalho não rastreado do checkout principal e os dois módulos C2 não rastreados do operador não foram alterados.

### O que a #76 já fechou

A #76 identifica o pareamento completado integral em dois argumentos, seu ledger de seis campos e o kernel de diferenças divididas cujos jets são os momentos canônicos, em toda ordem. Também refuta usar apenas o traço escalar normalizado como família de Gram.

Esta continuação não recompila ou reembala essa identificação como se fosse uma nova prova. Os novos módulos usam diretamente as definições originais do operador, nas mesmas versões, e investigam sua norma. A preservação integral do código da #76 é verificada contra o commit base.

### Resultados anteriores reutilizados

`CompletedC3FullWronskianOperatorCarrier.lean` fornece o estado completo do carrier operatório, seu quociente de câmera e o operador que lê o Wronskiano. O carrier é literalmente

\[
\mathcal H_{op}=\mathbb C^2\oplus(\mathbb C^2\oplus\mathbb C^2),
\]

com os produtos `WithLp 2` já existentes. Os três pares são o traço bruto ponderado, o traço Xi ponderado e o traço de câmera ponderado. Eles mantêm companions diferentes e não são estados equivalentes só porque algumas coordenadas escalares coincidem.

De `CompletedC3SymplecticCrossingNormalAudit.lean`, reutilizamos:

- `canonicalCompletedC3FullWronskianOperatorState_eq_analyticState`;
- `canonicalCompletedC3FullWronskianOperatorState_zero_eq_centralState`;
- `norm_canonicalCompletedC3FullWronskianOperator`;
- `canonicalCompletedC3FullOperatorCrossingNormal_eq_neg_operator`;
- `inner_crossingNormal_realSourceTangent_eq_normalization_mul_h0`.

O último já identifica o cruzamento linear da fonte com a normal. O mesmo módulo dá uma fórmula para a energia da projeção e uma condição de igualdade com `h0`; não demonstra essa igualdade.

`CompletedC3KernelMetricCalibration.lean` já exclui outra realização concreta, baseada na métrica ordinária/logarítmica/residual. Não tratamos essa obstrução anterior como novidade. Aqui a identidade nova é a decomposição completa do carrier de três traços e seus efeitos após a normalização canônica.

Somente nos controles finais usamos os resultados nativos anteriores `0<h0<1/16`. Eles não entram nas definições de estado, normal, tangente ou componente ortogonal.

## B — O que foi demonstrado agora

Os nomes novos pertencem ao namespace `CarryFullSource`.

### 1. O estado usa apenas as normalizações originais

`originalNormalizedState M z`, escrito `X_M(z)`, é o estado original do carrier depois dos dois fatores já prescritos:

\[
X_M(z)=\frac1{\sqrt2 F(z)}\,
  \frac1{C(z)}\,X^{raw}_M(z).
\]

`sourceNormalization z` é apenas o produto desses fatores. Não recebe momentos, sinais, zeros ou alturas. `original_state_eq_scaled` e `original_state_zero` identificam seu valor central com a fonte original independente do cutoff.

A normalização não foi escolhida para acertar uma energia: é a que já transforma o Wronskiano na resposta logarítmica do projeto.

### 2. Três coordenadas de valor permanecem explicitamente presentes

`three_value_coordinates` prova, para `s(z)` no `genuineCriticalStrip` e `F(z)≠0`,

\[
X_M(z)_{raw,value}=X_M(z)_{Xi,value}=X_M(z)_{C,value}=\frac1{\sqrt2}.
\]

São três papéis do carrier original. A prova preserva seus companions, os fatores de câmera, a completion e a norma do produto; não elimina os papéis por igualdade dos readouts escalares.

`full_state_mass_exact` dá a decomposição completa:

\[
\|X_M(z)\|^2=\frac32+
 |X_{raw,comp}|^2+|X_{Xi,comp}|^2+|X_{C,comp}|^2.
\]

Nenhum termo assinado foi transformado em norma: esta é a **norma Hilbert ordinária** do carrier, distinta do seu readout com o operador simplético. `full_state_mass_lower` e `center_mass_lower` concluem

\[
\|X_M(0)\|^2\geq\frac32.
\]

O resultado é independente de `M` e não usa qualquer momento ou desigualdade theta.

### 3. O cruzamento normalizado continua sendo linear em h0

Definimos, a partir dos objetos físicos existentes,

\[
N=-J_{full}X_0(0),\qquad
T=\alpha(0)T_{raw},\qquad
\alpha(z)=\frac1{\sqrt2F(z)C(z)}.
\]

`normalizedPhysicalTangent` é a tangente física original multiplicada pelo **valor central** da normalização. Não é definida como a derivada de um produto com fator variável. Nenhuma informação de momento determina essa definição.

`source_normalization_cancels_collision` prova o cancelamento exato da escala antiga do ledger:

\[
\overline{\alpha(0)}\alpha(0)D(0)=1.
\]

`normalized_normal_tangent_pair` então demonstra

\[
\langle N,T\rangle_{\mathbb C}=h_0.
\]

Não se exige `h0>0` nessa identidade. `normalized_normal_norm` usa a isometria já provada de `J_full`, de modo que

\[
m:=\|N\|^2=\|X_0(0)\|^2\geq\frac32.
\]

### 4. Componente ortogonal: o sinal é quadrado

`normalComponent` é a fórmula ortogonal padrão no mesmo carrier:

\[
P_NT=\frac{\langle N,T\rangle}{\|N\|^2}N.
\]

Sua pertinência à linha normal e a ortogonalidade do resíduo são provadas em `normal_component_mem_normal_line` e `normal_component_orthogonal_remainder`. Não se postula uma projeção com a resposta desejada como campo.

`normal_center_inner_zero` e `normal_component_invariant_along_center` provam que adicionar `a X_0(0)` à tangente não muda essa componente, para qualquer `a : ℂ`. Portanto, um termo central proveniente da derivada de uma normalização variável não pode reparar esse teste de energia.

`normal_component_energy_exact` e `normal_component_energy_upper` concluem:

\[
E_N=\|P_NT\|^2=\frac{h_0^2}{m}
\leq\frac23h_0^2.
\]

Esta é a energia da projeção, não o cruzamento linear. A norma não fornece o sinal de `h0` pela simples existência da projeção.

## C — Obstruções demonstradas e alcance exato

### Estado inteiro: excesso central

Com a cota nativa anterior `h0<1/16`, `full_state_native_mass_gap` prova para todo `M`:

\[
\|X_M(0)\|^2-h_0>\frac{23}{16}.
\]

`isometric_transport_not_native_mass` exclui **qualquer isometria linear real** desse mesmo estado como forma de acertar a primeira entrada Gram. Isso inclui transportes que preservem as duas quadraturas reais, não apenas mapas complexos.

`orthogonal_extension_not_native_mass` demonstra que adicionar componentes independentes por soma ortogonal também não resolve esse excesso. Isso não exclui uma síntese multibase com cruzamentos reais: tal síntese não é a simples extensão ortogonal testada.

### Operações que preservam o valor observado

`value_preserving_mass_lower` não exige isometria. Qualquer vetor no mesmo carrier que conserve **uma** das coordenadas de valor `1/sqrt(2)` tem energia pelo menos `1/2`.

Logo `value_preserving_operation_native_gap` dá, para qualquer operação ambiente `P` que preserve essa coordenada no estado central,

\[
\|P X_M(0)\|^2-h_0>\frac7{16}.
\]

Isso abrange uma projeção ortogonal com essa propriedade. Não é um teorema contra todos os quocientes ou todos os observáveis possíveis: a hipótese de conservação desse readout é explícita.

### Projeção normal: déficit central

Usando também o sinal nativo anterior `h0>0`, `normal_component_strict_small` prova

\[
E_N<\frac{h_0}{24}<h_0.
\]

`normal_component_not_native_mass` conclui que essa projeção tampouco representa a massa canônica. O vetor não foi definido a partir de `h0`; a identificação do cruzamento com `h0` só entra depois da construção física.

Assim, duas realizações diferentes foram testadas na norma original: o estado inteiro excede `h0`, e sua componente ortogonal na normal fica abaixo de `h0`. Não se escolheu uma constante intermediária para ajustar o resultado.

### Restrição para um outro carrier legítimo

`native_mass_value_readout_gain` fornece uma condição necessária quantitativa. Se um carrier candidato real tiver vetor `v` com energia exatamente `h0` e um readout linear contínuo `L` que conserve o mesmo valor normalizado,

\[
\|v\|^2=h_0,\qquad Lv=1/\sqrt2,
\]

então necessariamente

\[
\|L\|^2>8.
\]

O ganho é uma **conclusão**, não um novo peso escolhido para fazer a prova funcionar. Esse resultado não exclui um readout físico com norma maior, nem uma avaliação não limitada com domínio legítimo. Tampouco autoriza introduzir tal readout artificialmente.

## D — O que permanece aberto e validação

Não foi encontrada uma Gram positiva dos momentos canônicos na síntese física enriquecida completa. A norma do carrier operatório testado é diferente da energia assinada que produz o readout dos momentos. O carrier é uma realização existente do **operador de Wronskiano**, não uma realização já provada do produto interno da Hankel.

Os teoremas não excluem:

- jets produzidos por uma operação nativa diferente da imagem isométrica do estado-base;
- um transporte físico não isométrico com seus bordos e resíduos integralmente conservados;
- uma realização no carrier material/Cauchy anterior à projeção de traço;
- uma construção que mantenha o valor-base em um canal registrado separado e identifique a energia da variação por uma identidade independente.

Nenhuma dessas possibilidades foi recebida como hipótese resolvida. A positividade all-order, a independência de todos os prefixos e os consumidores Jacobi/alturas continuam condicionados à ponte física faltante. Os no-gos não são um STOP da teoria.

### Reprodução

```bash
cd research/full-source-gram-obstruction
python3 validate.py
python3 record_provenance.py
```

Os módulos novos são compilados explicitamente com `warningAsError=true`. O validador executa também builds focados, `lake build --wfail`, as auditorias Foundation/Geometry/Analysis e a preservação de todas as fontes da base. Não se alteram nem se recompilam campanhas numéricas de momentos.

`Audit.lean` imprime os axiomas e percorre tipos/corpos separando: fonte/features sem dependência da definição de momentos; identidades do cruzamento com os momentos sem sinais finitos; controles de incompatibilidade que usam explicitamente `0<h0<1/16`. Um passe final audita a união, permitindo apenas `propext`, `Classical.choice`, `Quot.sound`.

As provas não importam módulos de pesquisa anteriores por cache informal: usam apenas os módulos originais do operador e os três arquivos novos. As provas da #76 são preservadas e referenciadas; sua identificação do kernel não é assumida como uma isometria.

Os resultados, comandos, hashes, tempos e logs ficam em `evidence/validation.json`. Não se apresenta essa validação local como sucesso de CI externo.

Validação executada: **12 comandos, todos com saída zero**. São **27 teoremas, seis definições e uma abreviação**. A auditoria cobre **34 raízes e 6.353 constantes transitivas na união**; seus três grupos se sobrepõem e não são somados. Passaram os controles de escapes de confiança e de preservação.

## E — Próximo passo mínimo

A investigação deve sair da tentativa de identificar toda a norma do estado-base com o momento. A realização procurada precisa explicar a **variação orientada** que o cruzamento lê, mantendo o valor-base e os demais canais no registro completo.

Um teste concreto é voltar ao readout de bordo no carrier material/Cauchy **antes** da projeção contínua para os três traços: calcular sua norma efetiva ou seu domínio, preservando o mesmo dado observado. A desigualdade de ganho acima permite excluir de imediato um candidato com readout normativo pequeno; se a avaliação for não limitada, será necessário provar o domínio da fonte e dos jets, sem trocar a norma.

Depois, a obrigação continua sendo uma igualdade polarizada em dois argumentos para o kernel já identificado na #76, com seus bordos, retorno e completion. Uma estimativa de norma da tangente ou da sua projeção só controla o quadrado do cruzamento; não determina a orientação de sinal. Para a rota residual da #41, é precisamente essa orientação da energia assinada que ainda precisa de uma lei independente da fonte.

**Conclusão:** novos defeitos quantitativos excluem o estado inteiro, seus transportes isométricos, extensões ortogonais e a projeção normal nas realizações especificadas. O objetivo completo de uma Gram física positiva permanece aberto e ativo. Resultado PARTIAL, sem merge automático.

Fim do relatório.
