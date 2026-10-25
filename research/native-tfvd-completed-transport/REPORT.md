# Transporte TFVD da torre nativa e comutador do completamento

**PARTIAL.** O transporte da TFVD para o Green físico foi demonstrado na
torre real inteira. Na fonte completada original, de suporte finito arbitrário,
o defeito foi identificado como um comutador explícito do bracket com os pesos
da fonte. As duas pernas, a amplitude, os dois traços e os nove pareamentos
entre interior, bordo e defeito permanecem exatos. O sinal canônico all-order
continua aberto.

## A — O que já estava demonstrado

Base explícita: PR #92, commit
`c4bcc38389c592681cde11a2b379079d6abd0cc9`, ainda aberta em draft ao iniciar.
Branch desta investigação: `agent/native-tfvd-completed-transport`.
Main local e origin/main preservadas:
`59e53d863f4ef0ad998b0eb19fd3891c9839cc35`.
Operador consultado sem edição:
`bfeb10fd2425400fa38139903d12bf0599f02e53`.

Foram reutilizados, sem mudar fontes, pins ou métricas:

- Da PR #92: `CarryVerticalSynthesis.nativeSynthesis`, a síntese limitada
  `S : NativeGpreTowerHilbert →L[ℝ] CanonicalCompletedNativeChiralCauchyCarrier`,
  suas colunas literais, sua unicidade e suas duas quadraturas.
- De `RealCarryTfvd.lean`, `RealCarryWeightedValve.lean` e `RealCarryL2.lean`:
  os shifts, o bracket centrado, Green, trace, retorno e a identidade
  `carryWeightedVerticalTfvd_identity`.
- Do operador: `NativeLaguerre.physicalRadialAdvance`,
  `physicalGreenResolvent`, `physicalGreenResolvent_reconstruct`,
  `physicalGreenOperator` e sua positividade já demonstrada.
- Os coeficientes `NativeCauchyPorts.finiteTfvdBulk` e os estados
  `physicalCompletedFiniteSource` e
  `canonicalCompletedNativeRadialProjectiveChiralState`.
- A amplitude `completedNativeNormalizedPositiveChiralAmplitude`, o quociente
  `completedNativeHermiteBiehlerChiralQuotient` e a forma assinada
  `canonicalCompletedNativeProjectiveChiralForm`, incluindo seu fator `1/2`.

O transporte finito Green com resíduos já existia em
`NativePhysicalGreenResolvent.lean`. Não é apresentado aqui como descoberta
nova. O avanço é a ligação com a síntese limitada da torre inteira e a fórmula
do resíduo como comutador dos pesos originais com o bracket.

A PR #41 continua fornecendo a ortogonalização algébrica e o residual de Schur,
separados de seu sinal. Não foi usada positividade Hankel para construir o
transporte. H6/K6 e a realização de doze fontes não são entradas das provas.

## B — O que foi demonstrado agora

Todos os nomes novos abaixo pertencem a `CarryNativeTfvd`.

### 1. Deslocamento e numerador com os dois traços

Sejam `U` o shift unilateral vertical, `V` o backward shift, `M` o multiplicador
físico por `u`, e `S` a síntese da PR #92. Na torre real inteira:

\[
\boxed{SU=MS},\qquad
MSVx=Sx-x_0\phi_0,\qquad \phi_j(u)=\sqrt u\,u^j.
\]

Teoremas: `native_synthesis_shift`, `vertical_shift_backward_trace` e
`native_backward_numerator`. O termo central não foi apagado nem substituído
por uma inversa limitada de `M`.

O bracket original satisfaz `(B_η x)_0=0` e

\[
(B_\eta x)_{j+1}=\eta^{-1}x_{j+2}-2x_{j+1}+\eta x_j.
\]

Para `η≠0`, `vertical_numerator_two_traces` e
`physical_numerator_two_traces` demonstram exatamente

\[
\boxed{(I-\eta M)^2Sx
=\eta M S(B_\eta x)+x_0\phi_0+(x_1-2\eta x_0)\phi_1.}
\]

Os traços são dos coeficientes da torre. Não são o valor bruto da meia densidade
em `u=0`, que se anula. O índice vertical e o índice radial permanecem distintos.

### 2. A TFVD chega ao Green físico original

Para `0<η<1`, escreva

\[
\mathcal R_\eta=(I-\eta M)^{-1},\qquad
\mathcal G_\eta=\eta M\mathcal R_\eta^2.
\]

São os operadores físicos já existentes, com o mesmo carrier L² e o mesmo
multiplicador `(1-ηu)⁻¹`. Os teoremas `synthesized_tfvd`,
`physical_tfvd_reconstruction`, `physical_boundary_return` e
`physical_green_on_bracket` provam

\[
\begin{aligned}
Sx&=S(G_\eta B_\eta x)+S(R_\eta\operatorname{Tr}_\eta x),\\
Sx&=\mathcal G_\eta S(B_\eta x)
 +\mathcal R_\eta^2[x_0\phi_0+(x_1-2\eta x_0)\phi_1],\\
S(R_\eta(a,b))&=\mathcal R_\eta^2[a\phi_0+\eta(b-a)\phi_1],\\
S(G_\eta B_\eta x)&=\mathcal G_\eta S(B_\eta x).
\end{aligned}
\]

A última igualdade é afirmada **na imagem do bracket**, exatamente o interior
consumido pela TFVD. Não foi anunciada uma identificação adicional de todos
os operadores em domínios não tratados. As identidades valem para todo vetor
da torre ℓ², incluindo suas caudas, sem condição de sinal.

O parâmetro `η` continua sendo o parâmetro vertical. Pode-se especializá-lo
à razão `criticalVerticalAmplitudeRatio` já demonstrada para cada base; não
foi identificado com uma deformação centro–pernas livre.

### 3. Compatibilidade das duas quadraturas no core complexo

`coefficientQuadratures` conserva as partes real e imaginária dos mesmos
coeficientes finitos. `coefficient_tower_synthesis` demonstra que sua síntese é
literalmente `NativeLaguerre.physicalCauchySynthesis`.

`coefficient_real_bracket` e `coefficient_imag_bracket` identificam os dois
brackets reais com as duas quadraturas de `finiteTfvdBulk`. Assim,
`physical_finite_reconstruction` transporta a mesma reconstrução com dois
traços complexos, sem escolher novos vetores a partir dos momentos.

### 4. O defeito do completamento tem fórmula local

Para um peso diagonal qualquer `w`, defina, no suporte finito original,

\[
D_wc=(w_jc_j)_j,\qquad
C_\eta[w]c=B_\eta(D_wc)-D_w(B_\eta c).
\]

`completion_commutator_zero` e `completion_commutator_succ` provam

\[
\boxed{(C_\eta[w]c)_{j+1}
=\eta^{-1}(w_{j+2}-w_{j+1})c_{j+2}
 +\eta(w_j-w_{j+1})c_j,\qquad (C_\eta[w]c)_0=0.}
\]

É uma fórmula em qualquer ordem e para qualquer suporte finito, não uma
estimativa numérica. Ela mantém as contribuições de ambos os vizinhos.
`completion_commutator_product` conserva separadamente as duas contribuições
da composição multiplicativa:

\[
C_\eta[ab]c=C_\eta[a](D_bc)+D_a(C_\eta[b]c).
\]

`weighted_physical_reconstruction` fornece então a identidade vetorial

\[
\boxed{\mathcal S(D_wc)
=\mathcal G_\eta\mathcal S(D_wB_\eta c)
 +\mathcal T_\eta(D_wc)
 +\mathcal G_\eta\mathcal S(C_\eta[w]c),}
\]

onde `𝒮 c=∑c_jφ_j` e

\[
\mathcal T_\eta(v)=\mathcal R_\eta^2
 [v_0\phi_0+(v_1-2\eta v_0)\phi_1].
\]

O último termo não foi absorvido em outro operador nem removido pela escolha
de uma métrica. Os dois dados de bordo continuam na fórmula.

Em particular, na comparação normalizada da PR #92, a diferença vetorial
pedida entre o retorno por `Q` e o retorno TFVD transportado fica explícita:

\[
\boxed{\mathcal S(D_Qc)-\mathcal T_\eta(c)
=\mathcal G_\eta\mathcal S(D_QB_\eta c)
+[\mathcal T_\eta(D_Qc)-\mathcal T_\eta(c)]
+\mathcal G_\eta\mathcal S(C_\eta[Q]c).}
\]

É a especialização `w=Q` do teorema acima, seguida da subtração do mesmo
vetor de bordo; não é uma identificação entre os dois retornos. Para a fonte
projetiva completa, os pesos corretos são `A` e `AQ`, conservados a seguir.

### 5. Fonte completada original: amplitude uma vez, duas pernas e nove cruzamentos

Defina apenas abreviaturas dos pesos já existentes:

\[
A_{k,j}=\operatorname{completedNativeNormalizedPositiveChiralAmplitude}(z_{k,j}),
\quad Q_{k,j}=\operatorname{completedNativeHermiteBiehlerChiralQuotient}(z_{k,j}).
\]

`completed_source_weighted_identity` prova, no carrier original,

\[
\boxed{P_k(c)=\sqrt{k+1}\,
 (\mathcal S(D_{A_k}c),\mathcal S(D_{A_kQ_k}c)).}
\]

`P_k` é exatamente `physicalCompletedFiniteSource`, a síntese dos estados
`canonicalCompletedNativeRadialProjectiveChiralState`. A amplitude ocorre uma
única vez em cada perna. O completamento contido em `A` e `Q` permanece intacto.
O índice `k` aqui é radial, não profundidade vertical.

`completed_source_three_parts` aplica a reconstrução aos pesos **A e AQ** e
obtém `P_k=P_G+P_T+P_C`: Green, traços e comutador completos nas duas pernas.
Só depois dessa igualdade é tomada a forma assinada original. Para coeficientes
independentes `c,d`, `completed_source_nine_pairings` demonstra

\[
\boxed{\mathfrak B(P_k(c),P_k(d))
=\sum_{\alpha,\beta\in\{G,T,C\}}
 \mathfrak B(P_\alpha(c),P_\beta(d)),}
\]

com `𝔅((I,R),(I′,R′))=½(⟨I,I′⟩−⟨R,R′⟩)`, a forma original. Não foram
descartados os pareamentos mistos com o defeito. A identidade não se limita
à diagonal `c=d`.

## C — O que foi refutado e qual é o alcance

Para `η≠0`, `completion_commutator_vanishes_iff` prova

\[
(\forall c\text{ finito},\ C_\eta[w]c=0)
\iff (\forall j,\ w_j=w_0).
\]

Portanto, um peso não constante não pode comutar com esse bracket em todo o
core finito. A omissão universal do comutador exige uma constância que deve
ser demonstrada; não decorre da reconstrução TFVD.

Isso não é um contraexemplo à positividade canônica. Tampouco se afirma aqui
que cada comutador nativo seja não nulo em todo `k` ou em toda direção.
A caracterização é exata e seu alcance é essa realização diagonal específica.

Também permanece inválida a identificação automática entre o retorno TFVD,
determinado por dois traços, e a reflexão quiral, determinada pelos pesos da
fonte completada. Nesta investigação ambos foram conservados em suas funções
originais, e a diferença de transporte foi calculada.

## D — O que permanece aberto

O Green físico positivo já existente recebe agora o interior TFVD da torre
por uma identidade demonstrada. Isso não elimina a perna retornada nem os
termos de bordo e de comutador da fonte completada.

Não foi demonstrado o sinal da soma dos nove termos na direção crítica,
nem uma Gram positiva igual às Hankel canônicas em toda ordem. Não foi
pressuposta essa igualdade em uma estrutura com campos condicionais.

Os resultados infinitos desta rodada concernem à TFVD e à síntese na torre
real ℓ². As fórmulas completadas valem para **todo suporte finito**, com uma
única lei de coeficientes. Sua extensão a estados completados infinitos ainda
exige o domínio dos multiplicadores `D_A`, `D_AQ` e dos comutadores envolvidos.
Não foi afirmada uma limitação global desses multiplicadores.

O simples fato de diferenças de pesos tenderem a zero, em um limite radial,
não fornece um controle uniforme quando os coeficientes críticos crescem.
Também não basta que um termo de autopareamento se anule: os termos mistos
com `P_C` continuam presentes na identidade.

Nenhum momento, zero, altura, Jacobi ou pivô positivo foi usado para construir
os estados ou os operadores desta prova. A sequência canônica foi preservada.

## E — Próxima obrigação mínima e reprodução

O próximo alvo já tem entradas explícitas: as diferenças vizinhas de **A e AQ**
que aparecem em `completion_commutator_succ`, sintetizadas pelo mesmo `S` e
pareadas com os componentes Green e de bordo.

O primeiro teste pode usar `e₀`: a fórmula dá exatamente
`C_η[w]e₀=η(w₀−w₁)e₁`. O primeiro interior `e₂` mantém as contribuições em
`e₁` e `e₃`. Isso permite confrontar diretamente os pesos originais, sem
recalcular momentos nem introduzir uma Gram auxiliar.

Para avançar no sinal, é necessário obter das relações da fonte um controle
combinado desses termos e de seus cruzamentos nas direções críticas. Uma
estimativa recebida como hipótese, equivalente ao sinal do próprio pivô, não
fecharia a lacuna. O objetivo seguinte é uma lei para as diferenças dos pesos
originais que seja independente da positividade Hankel ainda procurada.

Reprodução, no servidor `llm`, no diretório desta investigação:

```bash
python3 validate.py
```

O script recompila somente os três módulos da PR #92 efetivamente importados,
verifica sua igualdade com a base, compila explicitamente os módulos novos com
`warningAsError=true`, executa os builds físicos e da raiz com `--wfail` e as
auditorias Foundation, Geometry e Analysis. Nesta execução, os 16 comandos
registrados passaram com código de saída zero.

`Audit.lean` contém `#print axioms` e percorre transitivamente tipos e corpos,
incluindo auxiliares privados. A auditoria de 36 raízes públicas encontrou
6.244 dependências, somente `propext`, `Classical.choice` e `Quot.sound`, e
nenhuma dependência da construção dos momentos canônicos ou de certificados
posteriores de positividade finita. São 30 teoremas e seis definições públicos.

Os comandos e os códigos de saída ficam em `evidence/validation.json`; fontes,
pins e estado das branches em `evidence/source-provenance.json`; a recompilação
da base em `evidence/upstream.json`. Logs textuais removem apenas espaços
finais; quando necessário o log bruto integral é mantido em `.raw.log.gz`.

A entrega segue em PR draft sobre a PR #92, sem merge automático. Main e
trabalhos anteriores permanecem preservados.

**Fim do relatório.**
