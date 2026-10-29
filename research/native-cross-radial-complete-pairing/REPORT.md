# Pareamento completo entre regularizações radiais independentes

**Classificação: PARTIAL para a positividade canônica all-order.**
O alvo desta rodada é a identidade física em dois índices radiais indicada
na PR #109, seguida do teste mínimo J0(k),J1(2k+1). Os resultados de
obstrução são específicos desse cruzamento bruto; não da geometria Carry.

Repositório: `thiagomassensini/geometry-of-numbers`.
Branch: `agent/native-cross-radial-complete-pairing`.
Base exata: `c7bf5781dee8edf5c4fcfc4c4c1153697d0f2a0b`, head da PR #109,
aberta e draft no reconhecimento. A nova PR fica empilhada sobre
`agent/native-mixed-imaginary-law`, sem merge automático.

## A — O que já estava demonstrado

A PR #108 forneceu `CarryMixedParity.source_mean_and_contrast`, identidade
VETORIAL das médias e contrastes dos dois canais, antes de seu pareamento;
`signed_mean_contrast`, identidade da forma complexa original; e
`complete_complex_pair`, com UMA regularização radial e dois inputs.

A PR #109 provou a lei imaginária em ordens arbitrárias, sempre na mesma
regularização. Em particular, para κ=k+1,

\[
\kappa G(J_{0,k},J_{1,k})\longrightarrow 2ih_1.
\]

`completed_source_three_parts` já reconstrói o vetor físico inteiro a
partir de Green/bulk, AMBOS os traços de bordo e o commutator de completion.
`response_synthesis_expansion` e `native_response_expansion` fornecem um
resto analítico da MESMA resposta original. Nenhuma dessas identidades
recebe positividade canônica como hipótese.

Os arquivos `completed-trace-kernel/CrossRadialGeometry.lean` e
`mixed-radial-jet-limit/MixedRadialLimits.lean` já registravam fatores e
defeitos entre regularizações em outros readouts. Não presumimos que esses
carriers/readouts sejam iguais ao investigado aqui; também não repetimos
a hipótese já refutada de que todos os cruzamentos brutos coincidam.

## B — O que foi demonstrado agora

### 1. Identidade complexa em dois índices independentes

`crossSignedPair k l c d` é apenas uma abreviação do pareamento assinado
ORIGINAL entre `physicalCompletedFiniteSource k c` e
`physicalCompletedFiniteSource l d`.

`complete_cross_pair` prova, sem escolher uma nova métrica,

\[
\boxed{
G(P_k(c),P_\ell(d))=\sqrt{\kappa_k}\sqrt{\kappa_\ell}
\left[K_{q_\ell}(c,d)+\overline{K_{q_k}(d,c)}\right].
}
\]

Aqui `crossScale` é literalmente o produto das duas amplitudes radiais
existentes; q_j abrevia `responseSamples (radialStep j)` e K é o kernel
Cauchy original. A resposta na primeira ordem é q_ℓ; na ordem conjugada,
é q_k. Igualar essas duas respostas fora da diagonal alteraria a fórmula.

Hipóteses exatas da identidade local: suportes finitos contidos nos
respectivos prefixos; característica não nula em cada prefixo; identidade
original incidente−retorno em cada prefixo. São hipóteses de regularidade,
não de sinais de Hankel, inversibilidade de Schur ou contratividade.

`cross_mixed_exact` descarrega essas condições EVENTUALMENTE para quaisquer
dois caminhos u,v tendendo a infinito, quaisquer suportes finitos S,T e
quaisquer coeficientes reais c,d nos jets originais. `cross_mixed_conjugate`
e `cross_mixed_real_zero` provam que o cruzamento continua puramente
imaginário, inclusive entre regularizações distintas. A parte real é lida
somente depois da síntese e do pareamento complexos completos.

`cross_scale_diagonal` e `cross_pair_diagonal` recuperam exatamente as
normalizações anteriores quando k=ℓ. Não se divide nenhum cruzamento para
forçar essa igualdade fora da diagonal.

### 2. Green completo antes da leitura

`cross_source_reconstruction` transporta AMBOS os estados inteiros para
suas três partes. `cross_source_nine_pairings` mantém todos os NOVE
cruzamentos entre bulk, bordo e commutator, em dois índices independentes.
A identidade vale para qualquer k,ℓ e inputs finitos, com 0<η<1.

`cross_green_four_blocks` agrupa essas nove parcelas em bulk+bordo,
dois cruzamentos ordenados com o residual e residual–residual. Nenhum
residual é apagado por isotropia presumida. `crossGreenPair` é a soma
literal dessas nove parcelas; `cross_green_eq_original` prova sua igualdade
com o pareamento original. Não é um operador ajustado.

### 3. O primeiro cruzamento de jets fora da diagonal

`first_cross_exact` computa a MESMA fonte J0(k),J1(ℓ), conservando os
dois pesos radiais. `doubled_first_exact` especializa ℓ=2k+1:

\[
G_k:=G(J_{0,k},J_{1,2k+1})
=i\sqrt2\,\kappa^2\left[q(\delta/2)-q(\delta)/3\right],
\qquad \delta=1/\kappa.
\]

Nesta fórmula q é o `responseReadout` nativo, não uma fonte substituta.
A expansão original q(z)=h0 z−h1 z³+z⁵R2(z) dá os coeficientes

\[
A=\frac{i\sqrt2}{6}h_0,\qquad
B=\frac{5i\sqrt2}{24}h_1,
\]

\[
E(z)=i\sqrt2\left[\frac{R_2(z/2)}{32}-\frac{R_2(z)}3\right].
\]

`doubled_remainder_continuous` prova continuidade desse resto da própria
fonte; `doubled_scaled_expansion` e `doubled_unscaled_expansion` provam
as identidades exatas eventuais

\[
\boxed{\delta G_k=A+\delta^2 B+\delta^4 E(\delta)},\qquad
\boxed{G_k=\kappa A+\delta B+\delta^3 E(\delta)}.
\]

Consequentemente, `doubled_scaled_tendsto` e `doubled_next_tendsto` provam

\[
\delta G_k\longrightarrow A,
\qquad \kappa(G_k-\kappa A)\longrightarrow B.
\]

A subtração na segunda fórmula é uma IDENTIDADE DIAGNÓSTICA, não uma
mudança da fonte ou do kernel físico. `doubled_green_scaled_tendsto`
transporta o primeiro limite à soma Green dos nove cruzamentos, sem
alterar nenhuma parcela. `doubled_imaginary_scaled_tendsto` faz a projeção
imaginária somente ao final.

### 4. Sinal e não anulação separados da extração

Todas as fórmulas e limites acima são provados SEM hipóteses de sinal.
`doubled_leading_eq_zero_iff` prova A=0 se e somente se h0=0.
`doubled_finite_limit_forces_h0_zero` prova que um limite complexo finito
do cruzamento bruto obrigaria h0=0.

Apenas a regressão estrita `doubled_no_finite_limit` reutiliza o teorema
PREEXISTENTE `canonicalCompletedNativeLogDerivativeMoment_zero_pos`.
Esse resultado de baixa ordem usa o fechamento theta/cosseno já existente;
não é apresentado como uma nova prova geométrica de h0>0. A dependência
fica isolada em um grupo próprio de auditoria. A extração física e os
coeficientes A,B não dependem desse certificado.

## C — O que foi refutado

O cruzamento bruto J0(k),J1(2k+1) NÃO tem limite complexo finito, pois
h0>0 já está demonstrado. Portanto ele não pode receber automaticamente
a mesma lei decrescente da diagonal J0(k),J1(k). O termo linear κ A
sobrevive na fonte original e tem coeficiente não nulo.

Esta é uma obstrução à identificação literal dessas duas regularizações
como se preservassem os mesmos cruzamentos de jets. Não demonstra uma
impossibilidade de transporte com complemento explícito. Não demonstra
uma direção negativa de H/K nem uma falha da teoria geométrica.

Ortogonalidade REAL entre paridades continua válida. Ela não permite
apagar a informação imaginária; neste teste, essa informação tem um
termo crescente. A coincidência de um readout real igual a zero não
identifica os estados nem seus pareamentos complexos.

## D — O que permanece aberto

Está provada a identidade em dois índices da própria fonte completada,
com a normalização literal, e está calculado o defeito no primeiro teste
misto. Não foi provada uma isometria de colagem entre regularizações,
uma lei positiva all-order ou uma nova realização Gram da Hankel canônica.

Também não se afirmou uma igualdade tipada entre esta construção e os
outros readouts radiais históricos. Os resultados anteriores de fatores
radiais permanecem válidos em seus próprios domínios.

As fontes, métricas, endereços, duas pernas, fases, amplitudes, retorno,
completion, Gamma, pins e trabalhos antigos foram preservados. O índice
k aqui é de REGULARIZAÇÃO RADIAL, não profundidade vertical do Carry.

## E — Próximo passo mínimo

O primeiro passo útil é localizar o termo κ A na RECONSTRUÇÃO VETORIAL
Green já existente, antes do pareamento. Para os jets J0(k),J1(2k+1),
provar quais componentes de bulk, dos DOIS bordos e do commutator originam
esse termo e quais cruzamentos o cancelam ou preservam. A soma dos nove
termos deve reproduzir exatamente A=i√2 h0/6, sem normalizar a fonte.

Isso exige uma identidade vetorial de comparação entre regularizações
com o complemento retido, não apenas subtrair κ A depois da escalarização.
Se esse transporte não existir no domínio físico, registrar o defeito
vetorial explícito. Se existir, confrontá-lo com a diagonal e com o
coeficiente seguinte B, antes de tentar uma lei uniforme na ordem.

O sinal das formas reais completas H/K ainda exige uma propriedade
independente da fonte. A extração de mais um coeficiente, isoladamente,
não a fornece e não deve ser apresentada como prova de positividade.

### Reprodução, auditoria e entrega

No host canônico llm, em checkout desta branch com o cache canônico:

```bash
cd research/native-cross-radial-complete-pairing
python3 validate.py
```

A execução normal recompila 49 ancestrais intactos da base. A opção
`--reuse-upstream` exige os hashes registrados de fontes E `.olean`.
Os quatro módulos novos e Audit são SEMPRE compilados explicitamente
com `lean -DwarningAsError=true`. Também se executam os builds pertinentes
com `lake build --wfail`, as auditorias Foundation/Geometry/Analysis e
as verificações de fontes, pins, main e trabalhos antigos.

**Os 15 checks locais passaram com código de saída zero.** São 31
teoremas novos, oito definições e uma abreviação: 40 raízes públicas.
Cada raiz tem `#print axioms` e uma inspeção transitiva de tipos E corpos:

| Grupo | Raízes | Dependências únicas | Restrição |
| --- | ---: | ---: | --- |
| Construção | 25 | 5.513 | Momentos canônicos proibidos; certificado h0 proibido |
| Proveniência e limites | 14 | 5.718 | Certificados de sinais proibidos |
| Regressão de obstrução | 1 | 5.260 | Permite o teorema preexistente h0>0 |

Todos os grupos permitem somente `propext`, `Classical.choice` e
`Quot.sound`; consumidores posteriores de positividade finita continuam
bloqueados. A auditoria de Foundation mantém suas regras próprias.
Não se reivindica footprint vazio para a camada analítica. Não há
`sorry`, `admit`, `native_decide` ou axiomas matemáticos novos.

`evidence/validation.json` registra comandos, logs, saídas e durações;
`evidence/lean-Audit.log` registra os certificados; `public-roots.json`
lista todas as raízes. `evidence/upstream.json` contém os hashes das
fontes E `.olean` dos 49 ancestrais recompilados da base exata.
`bootstrap.log` e seu registro preservam essa compilação.
`source-provenance.json`, `preservation.json` e `SHA256SUMS` registram
fontes, pins, arquivos antigos protegidos e integridade da entrega.
Quando foi necessário normalizar espaços finais dos logs, o log bruto
foi conservado em `.raw.log.gz` com hash registrado. Os checks locais
não são uma afirmação sobre sucesso de CI remoto.

A publicação é uma PR draft sobre a PR #109, sem merge em main.
O SHA do commit e a URL ficam na entrega externa. A cópia local arquivada
é conferida por manifesto SHA256 e pelo rodapé integral deste relatório
antes de remover somente a worktree criada nesta rodada.

**Fim do relatório — PARTIAL para positividade all-order; pareamento
complexo em dois índices provado e defeito do primeiro jet misto preservado.**
