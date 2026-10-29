# Transporte da primeira correção ao setor ímpar nativo

**PARTIAL para positividade canônica all-order; alvo E da PR #106
concluído.** A mesma energia completada admite agora o limite da primeira
correção para qualquer suporte finito de jets ímpares originais. A fase −i,
a conjugação, os fatoriais, os dois pareamentos ordenados e o resto são
mantidos. Nenhuma positividade de Hankel é recebida como hipótese.

Base exata: `277b981d09750be7ab72a7bb0072c948875ded24`, PR #106,
branch `agent/native-all-order-energy-correction`. Nova branch:
`agent/native-odd-energy-correction`. Main preservada:
`59e53d863f4ef0ad998b0eb19fd3891c9839cc35`.
Operador consultado: `bfeb10fd2425400fa38139903d12bf0599f02e53`.
Entrega em PR draft empilhada sobre #106, sem merge automático.

## A — O que já estava demonstrado

A PR #106 já provou o transporte da correção para somas finitas de jets
pares, a expansão vetorial do Taylor antes do pairing e a recomposição
Green completa. São reutilizados os seus restos `nativeRemainder N` da
mesma resposta, as operações de kernel e as provas de continuidade da
síntese ponderada. Não se constrói outra resposta nem outros momentos.

Da PR #105 reutilizam-se `static_odd_divided`, `divided_below`,
`difference_power_sum`, a definição `spatialCorrection` e os stencils
nativos. `static_odd_divided` aceita ordens arbitrárias dos stencils;
a restrição a peso ímpar é conservada.

A lei combinatória com paridade já existia. Nesta entrega entram como
**dependências formais efetivas** dois módulos históricos imutáveis:

- `all-order-binomial-green/ShiftedDifferences.lean`:
  `shiftedPower`, `shifted_power_sum`, `triangular`, `secondOffset`.
- `all-order-binomial-green/BinomialCoefficient.lean`:
  `mixedCoefficient`, `mixed_coefficient_leading`,
  `same_parity_first_correction` e `parityRadialCoefficient`.

Não se repetiu a prova da lei binomial. A nova ponte identifica sua
formulação real com a extração complexa do kernel usado na PR #106.

Continuam sendo usados os teoremas originais
`radial_jet_original_source`, `full_response_flux`, `full_split`,
`radial_weight_difference` e
`canonicalCompletedNativeRadialProjectiveChiral_eventually_regular`.
Eles conservam a fonte completada, seus dois canais e a regularidade.

A distinção da PR #41 permanece: eliminação algébrica não determina sinal.
Não há inverso ou direção crítica como entrada nesta rodada. k denota a
regularização radial, não a profundidade vertical do Carry; r,s são
índices de jets e j+1 continua sendo o endereço material amostrado.

## B — O que foi demonstrado agora

Os novos nomes pertencem a `CarryOddEnergy`.

### B.1 — A fase ímpar tem proveniência vetorial

`nativeOddProfile r` é somente a entrada estática original

\[
 o_r=(-i)(-1)^r\operatorname{staticStencil}(2r+1).
\]

`radial_odd_calibration` prova a igualdade de coeficientes

\[
\boxed{
\operatorname{radialJetCoefficients}(k,2r+1)
 =(k+1)^{2r+1}o_r.
}
\]

O fator −i é obtido do inverso do passo imaginário original. Não é uma
rotação escolhida depois de conhecer uma energia. `odd_profile_support`
deriva o suporte literal nos endereços 0,...,2r+1.

`odd_pair_static` avalia as duas fases conjugadas no produto interno
original: conj(−i)(−i)=1. A alternância (−1)^r e a do outro input continuam
na expressão. Só depois dessa igualdade complexa se aplica a extração
espacial. As fases não são apagadas no estado físico.

### B.2 — Reutilização exata da lei de paridade

`shifted_power_complex` identifica o `shiftedPower` histórico com o fatorial
vezes `differencePower`. `divided_coefficient_native` identifica as duas
extrações de dois índices, com os dois fatoriais originais.

`divided_first_odd` aplica o teorema existente
`same_parity_first_correction 1 r s`. O resultado para o coeficiente
normalizado complexo tem o sinal adicional negativo da paridade ímpar.
Não se renormaliza a métrica para compensá-lo.

Se K_p é o kernel Cauchy original ponderado por (j+1)^p, então
`odd_pair_below`, `odd_pair_leading` e `odd_pair_correction` provam:

\[
K_p(o_r,o_s)+K_p(o_s,o_r)=0
\quad(p=2l+1,\ l<r+s+1),
\]

\[
K_{2(r+s+1)+1}(o_r,o_s)+K_{2(r+s+1)+1}(o_s,o_r)
 =(-1)^{r+s+1},
\]

\[
K_{2(r+s+2)+1}(o_r,o_s)+K_{2(r+s+2)+1}(o_s,o_r)
 =(-1)^{r+s+1}A_{2r+1,2s+1},
\]

com os mesmos coeficientes espaciais já definidos:

\[
s_m=\frac{(m+1)(m+2)}2,\quad
 t_m=\frac{(m+1)(m+2)(m+3)(3m+4)}{24},\quad
 A_{m,n}=t_m+t_n-s_ms_n.
\]

A alternância dos coeficientes da resposta nativa se combina com esse
sinal, produzindo o termo +h_(r+s+1) na identidade algébrica;
isso não é uma demonstração de sinal desse momento ou da forma inteira.

### B.3 — O mesmo resto chega aos dois inputs completos

Com l=r+s+1, `odd_pair_taylor_cancellation` retém dois termos do Taylor.
`odd_pair_response_expansion` prova, em uma vizinhança do centro,

\[
\boxed{
\Psi^{\mathrm{odd}}_{rs}(z)=z^{2l+1}
 \left(h_l-z^2A_{2r+1,2s+1}h_{l+1}+z^4T_{rs}(z)\right).
}
\]

Psi é a soma dos DOIS pareamentos ordenados das sínteses com amostras da
mesma `responseReadout`. T_rs é a mesma soma com peso

\[
 (j+1)^{2l+5}R_{l+2}((j+1)z).
\]

A igualdade da síntese complexa inteira antecede essa leitura.
`odd_pair_remainder_continuous` reutiliza a continuidade da síntese da
PR #106 e prova a continuidade de T_rs. `normalized_odd_pair_expansion`
conserva exatamente o termo delta_k^4 T_rs(delta_k).
`normalized_odd_pair_correction_tendsto` calcula o limite da correção
reescalada. Não se presume que o resto tenha sinal.

### B.4 — Limite da mesma energia completada em qualquer suporte finito

Para S finito FIXO e c_r reais fixos, a fonte é a soma literal

\[
 f_k^{\mathrm{odd}}=\sum_{r\in S}c_r
    \operatorname{radialJetCoefficients}(k,2r+1).
\]

`finite_odd_source_original` prova a igualdade vetorial completa com
soma c_r J_(2r+1), nos dois canais. `finite_odd_source_support` fornece o
prefixo de endereços. `finite_odd_source_pairing` reúne os pares ordenados
por reindexação exata, mantendo todos os cruzamentos.

Se κ_k=k+1, defina as leituras da sequência canônica ORIGINAL

\[
 Q^{\mathrm{odd}}_S(c)=\sum_{r,s\in S}c_rc_s h_{r+s+1},
\qquad
 C^{\mathrm{odd}}_S(c)=-\sum_{r,s\in S}c_rc_s
 A_{2r+1,2s+1}h_{r+s+2}.
\]

`finite_odd_energy_pairing` descarrega a regularidade no prefixo da fonte.
O teorema principal é `finite_odd_energy_correction_tendsto`:

\[
\boxed{
\kappa_k^2\left(\operatorname{fullEnergy}(k,f_k^{\mathrm{odd}})
    -Q^{\mathrm{odd}}_S(c)\right)
\longrightarrow C^{\mathrm{odd}}_S(c).
}
\]

Em Lean, o coeficiente A é lido pela parte real de `spatialCorrection`, o
mesmo polinômio real acima. O resultado inclui suporte vazio e coeficientes
nulos. Não exige `PosDef`, `PosSemidef`, `IsUnit` de Hankel, whitening,
alturas ou sinal de pivô.

`finite_odd_green_recomposition` conserva exatamente
fullEnergy=bulkBoundaryEnergy+mixedEnergy, com o halo do comutador e
qualquer parâmetro original 0<eta<1. `finite_odd_green_correction_tendsto`
prova o mesmo limite para essa soma; nenhum setor é descartado.

`finite_odd_norm_difference_correction` conserva a normalização original
2 fullEnergy=norma_incidente²−norma_retornada² e transporta o limite para
esse balanço completo, com coeficiente 2 C_odd. A forma permanece assinada.

### B.5 — Regressões exatas e auditoria

`odd_profile_zero` prova o perfil (i,−i) nos dois primeiros endereços.
`odd_profile_one` prova o perfil cúbico (−i/6,i/2,−i/2,i/6).
São igualdades de coeficientes complexos, não apenas de normas.

`first_odd_correction` recupera, na mesma fonte J1,

\[
 (k+1)^2(\operatorname{fullEnergy}(k,\operatorname{radialJetCoefficients}(k,1))-h_1)\to-5h_2.
\]

`odd_cubic_source`, `odd_cubic_form`, `odd_cubic_correction` e
`odd_cubic_correction_tendsto` recuperam, para J3−aJ1,

\[
 Q=h_3-2ah_2+a^2h_1,\qquad
 C=-30h_4+84ah_3-5a^2h_2.
\]

São 35 teoremas, seis definições e uma abreviação em quatro módulos de
prova. A auditoria cobre 42 raízes: 21 espaciais com 5.106 dependências
transitivas e 21 de proveniência com 5.752 dependências. O primeiro grupo
proíbe momentos canônicos e característica; o segundo permite a resposta
original, mas rejeita os consumidores de sinais selecionados pelo guard.
Somente `propext`, `Classical.choice` e `Quot.sound` são permitidos.
Não há admissões ou novos axiomas matemáticos.

## C — O que foi refutado ou não pode ser inferido

`odd_coefficient_regression` prova A11=5, A13=42, A33=30.
`odd_coefficient_minor_negative` prova exatamente

\[
 A_{1,1}A_{3,3}-A_{1,3}^2=5\cdot30-42^2=-1614.
\]

Logo, também no setor ímpar, essa tabela de coeficientes não é uma Gram
positiva. O controle é da tabela A, não um pivô negativo da Hankel canônica.
Não se alterou a estrutura para contorná-lo.

A identidade de transporte não torna positiva uma diferença de duas
normas positivas. O sinal de C_odd tampouco determina, sozinho, o sinal do
limite Q_odd. Essas inferências continuam injustificadas.

## D — O que permanece aberto

Agora há teoremas de primeira correção da energia concreta em qualquer
suporte finito fixo nos setores par e ímpar. Isso não é uma prova de
positividade all-order de H ou K, nem uma representação Hilbert positiva
coerente de todos os momentos.

Não se demonstrou uniformidade das cotas na ordem, limite conjunto k,d→∞,
domínio de operador infinito ou desaparecimento de cauda material infinita.
A regularidade é eventual para cada prefixo finito.

Também não se reuniu nesta PR uma expansão conjunta para fontes com jets
pares E ímpares simultaneamente. Os cruzamentos par–ímpar não podem ser
apagados por analogia com os casos de mesma paridade.

## E — Próximo passo mínimo

Calcular o pareamento misto da MESMA síntese com uma entrada par e outra
ímpar independentes, mantendo seu valor complexo antes da parte real.
Para F_even(k,c), F_odd(k,d) nos dois canais originais, o primeiro alvo
concreto é determinar exatamente, para k suficientemente grande,

\[
\Re\mathfrak G(F_{\mathrm{even}}(k,c),F_{\mathrm{odd}}(k,d)).
\]

Investigar se a conjugação da resposta original força essa parte real a
zero, provando a igualdade vetorial correspondente antes de usá-la.
Se falhar, registrar o defeito. Não trocar a forma assinada por um produto
interno positivo nem presumir que o pareamento complexo inteiro seja zero.

O antecedente `radial-common-refinement/CommonJets.lean` já contém
`common_even_odd_jets`, um limite complexo zero no refinamento comum com
duas escalas. Foi conferido seu enunciado: não é uma identidade em k finito
nem um limite da correção reescalada por (k+1)². Não repetir esse resultado
como se resolvesse o novo alvo.

A compatibilidade exata permitiria reunir as duas expansões em uma única
fonte real com ambas as quadraturas. Ainda assim, o sinal exigirá uma lei
independente do transporte completado. O próximo trabalho deve preservar
essa distinção e evitar outra campanha de momentos ou pivôs já certificados.

### Reprodução e evidências

No ambiente original do host `llm`, em worktree desta branch com `.lake`
ligado ao cache canônico:

```bash
cd research/native-odd-energy-correction
python3 validate.py
```

O comando normal recompila os 37 ancestrais da base exata, incluindo os dois
módulos históricos da lei binomial. `--reuse-upstream` aceita somente o
bootstrap registrado cujos hashes de fontes e `.olean` coincidam.
Os quatro módulos novos e `Audit.lean` são sempre compilados explicitamente
com warnings como erros; o build raiz não inclui automaticamente pesquisas.

Os **15 checks locais passaram com código de saída zero**.
A validação inclui `lake build --wfail` raiz e dos alvos pertinentes do
operador, auditorias Foundation/Geometry/Analysis e verificação de base,
fontes, pins e trabalhos antigos. Comandos e resultados estão em
`evidence/validation.json`; a auditoria está em `evidence/lean-Audit.log`.
`evidence/upstream.json`, `evidence/source-provenance.json`,
`evidence/preservation.json`, `public-roots.json` e o manifesto SHA256
completam as evidências. Os checks locais não constituem afirmação de CI remoto.

**Fim do relatório — PARTIAL para positividade; transporte da primeira
correção da energia completada provado em qualquer suporte finito ímpar.**
