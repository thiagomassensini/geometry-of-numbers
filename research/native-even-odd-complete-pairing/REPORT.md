# Pareamento completo par–ímpar e síntese conjunta nativa

**PARTIAL para positividade canônica all-order; alvo E da PR #107
concluído.** A parte real do cruzamento entre quaisquer duas fontes finitas
originais, uma par e outra ímpar, é exatamente zero para k suficientemente
grande. O pareamento COMPLEXO foi calculado primeiro e não foi apagado.
A expansão conjunta das duas paridades também foi demonstrada.

Base exata: `2a81eaf5008cb8e2fb90ec202038399ab575f251`, PR #107,
branch `agent/native-odd-energy-correction`. Nova branch:
`agent/native-even-odd-complete-pairing`. Main preservada:
`59e53d863f4ef0ad998b0eb19fd3891c9839cc35`.
Operador consultado: `bfeb10fd2425400fa38139903d12bf0599f02e53`.
Entrega em PR draft empilhada sobre #107, sem merge automático.

## A — O que já estava demonstrado

As PRs #106 e #107 já provaram a primeira correção da mesma energia
completada, separadamente nos setores par e ímpar, em qualquer suporte
finito fixo. São reutilizados seus inputs, fases, fatoriais, Taylor,
restos analíticos e os teoremas de limite. Nenhum momento é recalculado.

A nova dependência física decisiva é
`completedNativeOperatorCharacteristic_neg_conj_from_nativeChannel`, em
`CarrySelfAdjointOperator/NativeCompletedCenteredReflection.lean`.
Seu enunciado é

\[
 F(-\overline z)=\overline{F(z)}.
\]

A declaração original conserva a conjugação do fator de completamento
Gamma e a do canal bracket nativo, termo a termo. Essa etapa não usa
paridade centrada, positividade de momentos ou medida theta positiva.
Não foi reconstruída outra característica para obter a reflexão.

Também são reutilizados `source_mean_response`,
`completed_source_contrast`, `completed_kernel_mixed_reduction`,
`completed_commutator_mixed_pairing`, `full_split` e a regularidade eventual
da característica e do canal Hermite–Biehler nos nós físicos.

O antecedente `common_even_odd_jets`, em
`radial-common-refinement/CommonJets.lean`, já fornece um limite complexo
zero num refinamento comum com duas escalas. Esta entrega não repete esse
limite: calcula o cruzamento na mesma escala radial finita e sua parte real.

A separação da PR #41 continua válida: a existência de uma leitura
ortogonal algébrica não torna positivos seus residuais. k continua sendo
índice da regularização radial, não profundidade vertical Carry.

## B — O que foi demonstrado agora

Todos os nomes novos estão em `CarryMixedParity`.

### B.1 — Reflexão da mesma resposta, com o completamento conservado

`rotatedCharacteristic` abrevia a característica original na coordenada
já usada, Fhat(z)=F(i z). `rotated_characteristic_reflection` transporta
DIRETAMENTE a reflexão nativa, obtendo

\[
 \widehat F(\overline z)=\overline{\widehat F(z)}.
\]

`rotated_derivative_reflection` deriva essa igualdade usando as regras
certificadas de conjugação da derivada. `response_rotated_derivative`
conserva a fase original da resposta:

\[
 R(z)=-F'(z)/(2F(z)),\qquad q(z)=-iR(iz)
       =\widehat F'(z)/(2\widehat F(z)).
\]

O sinal na última expressão vem das duas fases i; não é alteração da
resposta. `response_reflection`, `response_real_ray` e
`response_samples_real` provam

\[
 q(\overline z)=\overline{q(z)},\qquad
 \overline{q(t)}=q(t)\quad(t\in\mathbb R).
\]

Essas são identidades das funções totalizadas originais. A interpretação
como estado físico regular NÃO é estendida silenciosamente a polos: as
hipóteses de regularidade serão descarregadas no prefixo finito abaixo.

`even_coefficients_real` e `odd_coefficients_imaginary` mantêm os inputs
originais e provam, em cada endereço,

\[
 \overline{c_{\mathrm{even}}}=c_{\mathrm{even}},\qquad
 \overline{c_{\mathrm{odd}}}=-c_{\mathrm{odd}}.
\]

A fase −i dos jets ímpares continua nos vetores. A matriz Cauchy original
continua sendo 1/(i+j+2). `kernel_double_sum`, `kernel_real_imaginary` e
`kernel_imaginary_real` transportam essas identidades ao kernel complexo
em dois argumentos independentes.

### B.2 — Um kernel complexo completo, não uma inferência da diagonal

Escreva S(c) para a síntese Cauchy original e P_k(c) para seu estado
completado nos DOIS canais. `source_mean_and_contrast` conserva dois
vetores que determinam integralmente esse estado:

\[
 D_k(c)=P_k(c)_1-P_k(c)_2,\qquad
 M_k(c)=\tfrac12(P_k(c)_1+P_k(c)_2).
\]

Usam-se as identidades vetoriais preexistentes para D e M antes de parear.
`signed_mean_contrast` calcula sua forma bilinear original. O produto dos
fatores originais, incluindo sqrt(k+1) e sqrt(2), é provado em
`contrast_mean_scale`; não é ajustado por uma nova normalização.

Defina, apenas como notação do kernel existente,

\[
 K_k(c,d)=\langle S(c),S(q((j+1)\delta_k)d)\rangle_\mathbb C,
 \quad \delta_k=(k+1)^{-1},\quad\kappa_k=k+1.
\]

`complete_complex_pair` prova a identidade EXATA

\[
\boxed{
 \mathfrak G(P_k(c),P_k(d))
 =\kappa_k\left(K_k(c,d)+\overline{K_k(d,c)}\right).
}
\]

A regularidade e o suporte são as hipóteses operacionais desse lema local.
Não há positividade, inverso de Hankel, whitening, ou hipótese de simetria
de K. Os dois termos ordenados precedem a parte real. Para c=d, a fórmula
é compatível com o `full_response_flux` anterior.

### B.3 — O cruzamento par–ímpar é puramente imaginário

Para suportes finitos S,T independentes e coeficientes reais c,d, denote
por E_k a entrada `finiteJetSource S c k` e por O_k a entrada
`finiteOddJetSource T d k`. `mixedPair` é literalmente
G(P_k(E_k),P_k(O_k)), com a forma ASSINADA original.

`mixed_pair_exact` descarrega a regularidade no prefixo físico e prova,
para k suficientemente grande,

\[
\boxed{
 \operatorname{mixedPair}_k
 =\kappa_k\left(K_k(E_k,O_k)-K_k(O_k,E_k)\right).
}
\]

A diferença resulta da conjugação do segundo kernel, que é puramente
imaginário; não é uma simetrização presumida. `mixed_pair_conjugate`
prova a identidade complexa

\[
 \overline{\operatorname{mixedPair}_k}=-\operatorname{mixedPair}_k.
\]

Somente depois, `mixed_pair_real_zero` conclui

\[
\boxed{\Re\mathfrak G(P_k(E_k),P_k(O_k))=0.}
\]

Vale para quaisquer S,T,c,d fixos e finitos, não apenas para uma diagonal,
um cutoff de baixa ordem ou o limite k→infinito. A igualdade é eventual,
com regularidade efetiva; não é reivindicada em nós físicos singulares.
É separação na forma real assinada, não uma realização Hilbert positiva.

`mixed_pair_green_recomposition` conserva ainda, em COMPLEXO,
o pareamento bulk/bordo com os dois termos ordenados de correção
Green-comutador. O halo exterior está na hipótese de regularidade.
Não se conclui que as parcelas dessa decomposição desapareçam separadamente.

### B.4 — Fonte conjunta e primeira correção dos dois setores

`jointJetSource` é somente E_k+O_k. `joint_source_original` prova sua
igualdade vetorial com a soma literal de todos os jets pares e ímpares nos
dois canais. A informação complexa não é quocientada ou eliminada.

`full_energy_add` primeiro conserva o termo 2 Re G(E,O).
`joint_energy_add` usa a igualdade REAL recém-demonstrada e conclui,
eventualmente,

\[
 E_{\mathrm{joint},k}=E_{\mathrm{even},k}+E_{\mathrm{odd},k}.
\]

Se Q_even,Q_odd e C_even,C_odd são as mesmas formas e correções canônicas
originalmente definidas nas PRs #106/#107, então
`joint_energy_correction_tendsto` prova

\[
\boxed{
 \kappa_k^2\bigl(E_{\mathrm{joint},k}-(Q_{\mathrm{even}}+Q_{\mathrm{odd}})\bigr)
 \longrightarrow C_{\mathrm{even}}+C_{\mathrm{odd}}.
}
\]

Os restos dos dois teoremas anteriores continuam controlados; o cruzamento
foi calculado exatamente, sem orçamento absoluto de caudas para apagá-lo.
`joint_green_recomposition`, `joint_green_correction_tendsto` e
`joint_norm_difference_correction` conservam bulk, bordo, termo misto e
o fator ORIGINAL 2 entre energia assinada e diferença de normas quadráticas.
Não se demonstrou aditividade separada de cada norma de canal nesta PR.

### B.5 — O menor cruzamento complexo conserva informação

`firstMixedPair k` é a forma original entre os jets J0 e J1.
`first_mixed_exact` prova, eventualmente,

\[
\boxed{
 \mathfrak G(J_0,J_1)
 =\frac{i\kappa_k^2}{3}\left(2q(\delta_k)-q(2\delta_k)\right).
}
\]

J0 usa sua entrada original +e0; o sinal histórico de `seedInput=-e0`
não é confundido com esse jet. A constante 1/3 vem da métrica Cauchy.

`first_mixed_scaled_expansion` retém o MESMO resto R2 da resposta nos dois
endereços e prova

\[
 \kappa_k\mathfrak G(J_0,J_1)=2ih_1+\delta_k^2\mathcal E(\delta_k),
\qquad
 \mathcal E(z)=\frac{i}{3}\left(2R_2(z)-32R_2(2z)\right).
\]

`first_mixed_error_continuous` prova sua continuidade e
`first_mixed_scaled_tendsto` conclui κ_k G(J0,J1)→2ih1.
Não se usam alturas, zeros ou sinal de um momento para calcular essa taxa.

### B.6 — Auditoria e evidências

São 37 teoremas, cinco definições e uma abreviação em quatro módulos de
prova. A auditoria cobre 43 raízes: 11 espaciais com 5.077 dependências
transitivas e 32 de proveniência com 5.780 dependências.
O grupo espacial proíbe momentos e característica; o de proveniência usa
apenas a resposta original e rejeita os consumidores de sinal selecionados
pelo guard. Só são permitidos `propext`, `Classical.choice` e `Quot.sound`.
Não há admissões nem novos axiomas matemáticos.

## C — O que foi refutado ou precisa ser distinguido

A identificação entre parte real nula e pareamento complexo nulo não é
uma inferência válida. O coeficiente radial calculado para J0,J1 é 2ih1.
`complex_orthogonality_would_force_h1_zero` dá um controle formal
**condicional**: se G(J0,J1) fosse eventualmente zero como número complexo,
então h1=0. A nova prova não recebe nem usa o sinal de h1 para computar o
kernel. Não se apresenta essa implicação como uma nova prova incondicional
de não anulação ou como obstrução à geometria completa.

Também não se conclui positividade de H ou K da separação entre paridades:
a forma conjunta continua sendo a diferença assinada dos mesmos canais.
A ortogonalidade real obtida não fornece o sinal dentro de cada setor.

## D — O que permanece aberto

A positividade all-order de H e K, a Gram Hilbert positiva canônica e o
transporte isométrico positivo da forma completa permanecem abertos.
A resposta conjugada foi transportada às identidades vetoriais e ao
pareamento original; não se construiu uma nova isometria entre carriers.

O controle é para suportes finitos fixos. Não há cota uniforme na ordem,
limite conjunto k,d→infinito, domínio de operador infinito ou descarte de
caudas materiais infinitas. As hipóteses locais da fonte são descarregadas
por regularidade eventual, não removidas no domínio inteiro.

A taxa imaginária foi formalizada para J0,J1. A lei em dois índices gerais
sugerida abaixo ainda não foi provada em Lean.

## E — Próximo passo mínimo

Extrair o PRIMEIRO coeficiente imaginário do cruzamento misto em quaisquer
dois índices, conservando o mesmo kernel completo e o resto. Para os
suportes independentes desta PR, a candidata concreta é

\[
\boxed{
 \kappa_k\operatorname{mixedPair}(S,T,c,d,k)
 \longrightarrow
 i\sum_{r\in S,s\in T}c_rd_s
    \bigl(s_{2s+1}-s_{2r}\bigr)h_{r+s+1},
 \qquad s_m=(m+1)(m+2)/2.
}
\]

Para r=s=0, recupera o 2ih1 já demonstrado. A redução espacial candidata
usa o peso ímpar m+n+2 com m=2r,n=2s+1; dois termos de diferenças finitas
devem sobreviver. Reutilizar os stencils, as fases e as somas de diferenças
já existentes; não fabricar uma métrica nem reconstruir momentos.

`mixed_rate_canary.py` testa essa candidata espacial em 25 pares
0≤r,s≤4, com `Fraction`, sem momentos como inputs. Conserva os dois
kernels ordenados separadamente e testa os cancelamentos ímpares inferiores.
O artefato se declara `PASS_FINITE_RATIONAL_ONLY`: o teste não prova a
convergência física nem a lei all-order candidata.

Essa obrigação recupera informação imaginária, não substitui a obrigação
de sinal das Hankel. Uma prova de positividade ainda exige uma lei
independente da fonte que controle sua forma assinada completa.

### Reprodução

No ambiente original de `llm`, em worktree desta branch com `.lake` ligado
ao cache canônico:

```bash
cd research/native-even-odd-complete-pairing
python3 validate.py
```

O comando normal recompila os 41 ancestrais da base exata. A opção
`--reuse-upstream` aceita somente os hashes registrados de fontes e `.olean`.
Os quatro módulos novos e Audit são sempre compilados explicitamente com
warnings como erros. A validação inclui `lake build --wfail` raiz e dos
alvos pertinentes do operador, auditorias Foundation/Geometry/Analysis,
o canário racional separado e a preservação de fontes, pins e trabalhos
preexistentes. O snapshot inicial de proveniência é comparado antes de
ser atualizado, inclusive os hashes dos arquivos antigos não commitados.

Os **16 checks locais passaram com código de saída zero**, incluindo
o teste racional, que permanece separado das provas Lean.

`evidence/validation.json`, `evidence/lean-Audit.log`,
`evidence/mixed-rate-canary.json`, `evidence/upstream.json`,
`evidence/source-provenance.json`, `evidence/preservation.json`,
`public-roots.json` e o manifesto SHA256 registram as evidências.
Checks locais não constituem afirmação sobre CI remoto.

**Fim do relatório — PARTIAL para positividade; cruzamento real par–ímpar
calculado e expansão da fonte conjunta demonstrados sem apagar o kernel complexo.**
