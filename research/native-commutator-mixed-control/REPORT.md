# Comutador da fonte completada: pernas iguais e cruzamento não nulo

**Classificação: PARTIAL.** A lei de pesos da fonte original elimina exatamente
o autopareamento assinado do comutador TFVD da PR #93. Ela não elimina seus
cruzamentos. No primeiro jet nativo, a correção mista completa tem limite
estritamente negativo. A positividade Hankel em toda ordem permanece aberta.

Base: `655e63b4d78aaefe3a442dabf945c2df698d2a59`, head da PR #93,
branch `agent/native-tfvd-completed-transport`. Esta continuação usa a branch
independente `agent/native-commutator-mixed-control`, com destino à PR #93.
Não presume a integração das PRs anteriores à main e não realiza merge.
O operador consultado permanece em
`bfeb10fd2425400fa38139903d12bf0599f02e53`.

## A — O que já estava demonstrado

A PR #92 construiu a síntese das colunas físicas originais
`φ_j(u)=sqrt(u) u^j`, preservando as duas quadraturas reais e o limite de cauda.
A PR #93 transportou a TFVD para essa síntese e recompôs a fonte completada:

\[
P_k(c)=P_G(c)+P_B(c)+P_C(c).
\]

`P_G` contém o Green do bulk; `P_B`, os dois traços de bordo independentes;
`P_C`, os comutadores dos pesos originais. Os teoremas reutilizados são
`CarryNativeTfvd.completed_source_weighted_identity`,
`completed_source_three_parts`, `completed_source_nine_pairings`,
`completion_commutator_zero` e `completion_commutator_succ`.
Eles se encontram em `research/native-tfvd-completed-transport/`.

Para `0<η<1`, o Green físico existente é
`G_η=η M_u (I-η M_u)⁻²`; não foi substituído por uma identidade.
A forma polarizada original permanece

\[
\mathfrak B((x_+,x_-),(y_+,y_-))
=\tfrac12(\langle x_+,y_+\rangle-\langle x_-,y_-\rangle).
\]

Na convenção Lean, o produto interno complexo é conjugado no primeiro
argumento. Sua parte real fornece a leitura real depois da síntese completa.
Não se modifica a métrica física de cada canal.

O mecanismo abstrato de média/contraste e o fato de um residual com pernas
iguais ser nulo para a forma assinada já apareciam em
`research/mean-contrast-green/MeanContrast.lean` e na investigação
`research/radial-green-intertwiner/`. Não são reivindicados como descoberta
desta rodada. A novidade é identificar **o comutador específico da PR #93**,
com o halo de domínio correto, e calcular seus cruzamentos na fonte original.

A ortogonalização algébrica da PR #41 continua distinta de uma norma de
Hilbert: inversibilidade do bloco anterior permite escrever o residual, mas
não determina seu sinal. Esta investigação não acrescenta `PosDef` a essa etapa.
As declarações finitas de H6/K6 e das doze fontes também permanecem intactas;
não são premissas da construção atual nem uma prova all-order.

## B — O que foi demonstrado agora

### B.1 — Lei exata das amplitudes originais

Escreva `F` para `completedNativeOperatorCharacteristic`,
`R=-F'/(2F)` para a resposta completada existente e

\[
A(z)=\frac{-F'(z)+iF(z)}{\sqrt2 F(z)},\qquad
Q(z)=\frac{-F'(z)-iF(z)}{-F'(z)+iF(z)}.
\]

Quando `F(z)≠0` e a coordenada positiva do denominador de `Q` não se anula,

\[
\boxed{A(z)-A(z)Q(z)=\kappa=2i/\sqrt2\ne0},\qquad
\boxed{A(z)=(2R(z)+i)/\sqrt2}.
\]

São `chiral_weight_difference` e `incident_amplitude_response`, em
`NativeWeightLaw.lean`. A constante é consequência das definições existentes;
não se escolheu nova normalização. Os valores são avaliados nos endereços
radiais originais `z_{k,j}=i(j+1)/(k+1)`.

`radial_weight_difference_eventually N` reutiliza a regularidade já provada da
fonte: para todo prefixo finito, a identidade vale eventualmente em todos os
seus endereços. Isso não consome sinal de momento ou de pivô.

### B.2 — Comutador comum, sem apagar o vizinho externo

Se `c` tem suporte em `{0,...,N-1}`, a fórmula preexistente é

\[
(C_\eta[w]c)_{j+1}
=\eta^{-1}(w_{j+2}-w_{j+1})c_{j+2}
 +\eta(w_j-w_{j+1})c_j,
\qquad (C_\eta[w]c)_0=0.
\]

É preciso conservar também o peso no endereço **N**: o termo que sai do
último coeficiente pode sobreviver. Sob regularidade no prefixo de tamanho
`N+1`, provamos

\[
\boxed{C_\eta[A_k]c=C_\eta[A_kQ_k]c
=\frac2{\sqrt2}C_\eta[R_k]c}.
\]

`commutator_equal_of_constant_difference` e `native_commutator_response`, em
`NullCommutator.lean`, são identidades vetoriais de coeficientes, antes da
síntese ou do pareamento. Nenhum controle de sinal é pressuposto.

Defina `E_k(c)` como a primeira perna do componente físico `P_C(c)` já definido
na PR #93. Então

\[
P_C(c)=(E_k(c),E_k(c)),\qquad
\mathfrak B(P_C(c),P_C(d))=0.
\]

`completed_commutator_equal_legs` e `completed_commutator_pairing_zero`
preservam dois argumentos independentes. O zero é polarizado; não se trata
apenas de igualdade entre duas normas diagonais.

### B.3 — Redução dos nove setores, mantendo os quatro cruzamentos

Ponha `s_k=sqrt(k+1)`, `S=physicalCauchySynthesis` e
`X_k(c)=s_k κ S(c)`. Da mesma lei da fonte segue

\[
P_k(c)_+-P_k(c)_-=X_k(c).
\]

`completed_source_contrast` prova esta identidade vetorial.
`completed_kernel_mixed_reduction`, em `MixedReduction.lean`, prova

\[
\boxed{\begin{aligned}
\mathfrak B(P_k(c),P_k(d))={}&
\mathfrak B((P_G+P_B)(c),(P_G+P_B)(d))\\
&+\tfrac12\bigl(\langle E_k(c),X_k(d)\rangle
                   +\langle X_k(c),E_k(d)\rangle\bigr).
\end{aligned}}
\]

Os setores `C–G`, `C–B`, `G–C`, `B–C` foram somados exatamente contra o
contraste da mesma fonte completa. Não foram removidos, majorados por zero ou
substituídos por normas. Os quatro setores internos de `G+B` também permanecem.

### B.4 — Costura aos jets nativos, sem amplitude duplicada

`NativeJets.lean` reutiliza a matriz existente
`nativeSourceChiralJetInputMatrix`. Seu coeficiente **já contém A**.
`rawJetCoefficients` retém os mesmos pesos de diferença finita, fases, fatoriais
e passo radial, antes desse único fator A. Não divide por uma amplitude nem
usa os momentos para definir vetores.

`raw_jet_original_source` prova a igualdade do par físico inteiro

\[
P_k(\operatorname{finiteEmbedding}(\operatorname{rawJetCoefficients}(n,k,v)))
=\operatorname{nativeSourceProjectiveBoundaryJetSynthesis}(n,k,v).
\]

`native_jet_commutator_eventually_null` alcança todo `n` e quaisquer dois vetores
`v,w : Fin(2n)→ℂ`. A eventualidade é uniforme nos coeficientes desse prefixo:
permite vetores críticos dependentes de k, inclusive crescentes. Não afirma um
único k válido para todas as ordens ou um limite uniforme em n.

### B.5 — Primeiro teste completo: cruzamento negativo da fonte real

Para `c=e₀`, `seed_is_native_zero_jet` identifica `P_k(e₀)` com o jet original
`projectiveChiralDifferenceJet k 0`. Não é um vetor de teste ajustado aos momentos.
Mantendo o vizinho externo, `commutator_seed` e `physical_commutator_seed` dão

\[
C_\eta[A_k]e_0=\eta(A_{k,0}-A_{k,1})e_1,
\quad E_k(e_0)=s_k\eta(A_{k,0}-A_{k,1})G_\eta\phi_1.
\]

Se `J_η=⟨φ₀,G_η φ₁⟩`, provamos, no espaço físico original,

\[
\boxed{J_\eta=\eta\|(I-\eta M_u)^{-1}\phi_1\|^2>0}.
\]

São `green_seed_cross` e `green_seed_cross_re_pos`, em `GreenSeed.lean`.
A prova usa a autoadjunção e as inversas do resolvente já construído, além de
`M_u φ₀=φ₁` e `φ₁≠0`. Não depende dos momentos canônicos.

Defina a correção mista completa, com ambos os ordenamentos,

\[
Z_k=\Re\{\mathfrak B(P_C(e_0),P_k(e_0))
             +\mathfrak B(P_k(e_0),P_C(e_0))\}.
\]

`seed_mixed_exact` conserva a expressão exata

\[
Z_k=\Re\{(k+1)\eta\bar\kappa(A_{k,0}-A_{k,1})J_\eta\}.
\]

Agora, e somente agora, usamos a identificação analítica **preexistente** da
derivada da resposta em zero com `h₀`:

\[
(k+1)(A_{k,0}-A_{k,1})\longrightarrow-i\,2h_0/\sqrt2,
\quad\boxed{Z_k\longrightarrow-2\eta h_0\Re J_\eta<0}.
\]

`SeedMixedLimit.lean` prova o limite, `seed_mixed_eventually_negative` e
`seed_commutator_eventually_nonzero`. O sinal estrito reutiliza explicitamente
`canonicalCompletedNativeLogDerivativeMoment_zero_pos`. Esse resultado anterior
vem da certificação da fonte theta; esta rodada **não** fornece uma nova prova
puramente geométrica de `h₀>0`. A identidade e o limite são separados do uso do
sinal na auditoria.

## C — O que foi refutado

1. **Descartar este comutador por seu autopareamento nulo.** O próprio jet nativo
   fornece um componente eventualmente não nulo e um cruzamento não nulo.
2. **Esperar uma correção mista sempre não negativa nesta decomposição.** Para
   todo `0<η<1`, o primeiro jet tem correção mista eventualmente negativa.
3. **Ignorar o endereço externo ao suporte.** Mesmo `e₀` produz um termo em `e₁`
   que contém o peso no endereço 1. Nenhuma truncagem desse termo foi usada.

Isto não demonstra pivô negativo, falha da fonte ou impossibilidade de uma
realização Gram completa. O balanço total inclui `G+B` e esta correção.
O sinal negativo encontrado é compatível com o sinal positivo conhecido de
`h₀`. Também não se identifica este componente com resíduos de decomposições
históricas que distribuem os termos de bordo de outra maneira.

## D — O que permanece aberto e como foi auditado

Falta determinar o sinal da **soma completa**, nas direções críticas de ordem
arbitrária, a partir de uma lei independente da positividade Hankel desejada.
A nova identidade localiza o comutador na resposta nativa e reduz seus quatro
cruzamentos a dois pareamentos completos; ela não determina esse sinal geral.

Não se demonstrou uma Gram positiva igual à Hankel canônica, uma isometria
global entre os estados nativos e theta, nem a extensão dos multiplicadores
`D_A`, `D_AQ` a todo o espaço infinito. O domínio provado nesta rodada é suporte
finito com o halo explícito. A pequena diferença de pesos, isoladamente, não
controla produtos com coeficientes críticos crescentes.

São **35 teoremas e cinco definições públicos**, em seis módulos. `Audit.lean`
executa `#print axioms` e percorre tipos e corpos, incluindo auxiliares privados,
em três grupos:

| Grupo | Raízes | Dependências transitivas | Dependência permitida |
| --- | ---: | ---: | --- |
| Construção e identidades físicas | 35 | 5.876 | Sem a sequência canônica e sem seus sinais |
| Extração analítica do coeficiente | 3 | 5.687 | h₀ como coeficiente, sem positividade de h₀ |
| Teste finito de sinal | 2 | 5.451 | h₀>0 preexistente, explicitamente identificado |

Todos os grupos rejeitam axiomas além de `propext`, `Classical.choice` e
`Quot.sound`, e rejeitam consumidores posteriores selecionados de positividade.
Não se usa `sorry`, `admit`, `native_decide` ou novos axiomas matemáticos.
O log de `lean-Audit` registra os totais transitivos efetivamente encontrados.
Os grupos se sobrepõem; os três totais não devem ser somados.

Os comandos reproduzíveis estão em `validate.py`: recompilação dos oito
ancestrais realmente importados, build físico focado, sete compilações explícitas
incluindo Audit, `lake build --wfail`, auditorias Foundation/Geometry/Analysis,
preservação da base e verificação de whitespace. Os resultados efetivos ficam
em `evidence/validation.json`. A raiz Lake não inclui automaticamente estes
módulos de pesquisa; por isso sua compilação explícita é indispensável.
Nesta execução, **os 17 comandos passaram com código de saída zero**; as
verificações finais de preservação também passaram.

Fontes e pins são registrados em `evidence/source-provenance.json`, os ancestrais
em `evidence/upstream.json`. `evidence/preservation.json` verifica os hashes das
fontes e dos trabalhos antigos protegidos. Os logs textuais removem somente
espaços finais; havendo alteração, o log bruto integral fica em `.raw.log.gz`,
com o hash do conteúdo original registrado. As provas históricas H6/K6 não foram
recompiladas nesta rodada; seus arquivos permanecem idênticos à base.
`MANIFEST.sha256` permite conferir os arquivos entregues com
`sha256sum -c MANIFEST.sha256`, nesta pasta.

## E — Próximo passo mínimo

Aplicar a redução exata à primeira direção crítica par não constante
`J₂-a J₀`, mantendo a inicialmente livre e só depois substituindo
`a=h₁/h₀` na direção já definida. As entradas para isso são os
`rawJetCoefficients` originais e o único comutador `C_η[R_k]`.

O alvo é identificar o primeiro termo finito e o resto analítico da **soma**
`G+B+misto`. Se surgirem termos divergentes nas partes, provar seu cancelamento
antes de extrair sinais. Não basta controlar `P_C` isoladamente, nem extrapolar
o sinal negativo do primeiro jet para outras ordens. A eventualidade uniforme
nos coeficientes já permite inserir a direção radial crítica sem reconstruí-la.

Só depois se deve buscar uma lei da resposta completada que controle essa soma
em toda ordem, preservando o mesmo kernel, as duas quadraturas, o bordo e a cauda.
A lei nova desta rodada é independente de positividade Hankel; o sinal geral
continua sendo a obrigação matemática que ela ajuda a formular.

Reprodução no servidor `llm`, na pasta desta investigação:

```bash
python3 validate.py
```

Entrega em PR draft sobre a PR #93, sem merge automático. Main, pins, fonte,
pesos e mudanças antigas permanecem preservados.

**Fim do relatório.**
