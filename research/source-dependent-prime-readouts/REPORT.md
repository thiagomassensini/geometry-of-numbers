# Readouts dependentes da fonte, porta Mellin e defeito Green preservado

**Classificação: PARTIAL.** Construídos e verificados o projetor primo com
readouts dependentes do input e uma porta Mellin exata nas somas finitas das
features físicas originais. A comparação com a métrica e o retorno nativos
produziu dois NO-GOs locais, com defeitos explícitos. A positividade canônica
all-order permanece aberta.

Data: 25/10/2026. Repositório `thiagomassensini/geometry-of-numbers`.
Branch `agent/source-dependent-prime-readouts`, baseada em
`d17aba9dfd0aa53a7b677cbb3da0e1e6213e0a54` da PR #89.
A PR anterior permanece intacta e ainda aberta; não se presume integração
à main. Entrega draft, sem merge automático. Execução em `ssh llm`.

## A — O que já estava demonstrado e o que foi reaproveitado

A PR #89 provou a fórmula binomial de extração radial em índices arbitrários
e identificou a limitação afim de P09: realizar os MESMOS readouts fixos para
toda uma família linear força o estado ativo a zero. A presente tarefa
constrói a extensão homogênea apropriada, sem receber positividade canônica.

O transporte dependente da fonte JÁ EXISTIA no operador:

- `RealFirstNative.primeContractionLinear` é o mapa real-linear T;
- `nativeGprePrimeCarryDefectState_apply` calcula cada fibra;
- `inner_globalCarryAxis_nativeGprePrimeCarryDefectState` recupera o readout;
- `nativeGprePrimeCarryDefectState_norm_sq_le` dá ||TX||²≤(11/12)||X||².

Seu domínio é `NativeGpreTowerHilbert = lp (N -> real) 2`; o contradomínio é
`PrimeCarryDefectGlobalHilbert`, soma Hilbert das fibras de resíduos primos.
O readout é o produto interno com o perfil p^(-j)/j, com nível zero separado.
A constante 11/12 decorre do orçamento aritmético já provado, sem sinal de
momentos ou hipótese Genuine-zero. Esse transporte não foi reconstruído.

Os eixos originais psi_p e seus duais psi_p^vee, com
<psi_p,psi_p^vee>=1 e ||psi_p^vee||²=p/(p-1), são reutilizados literalmente.
Também são reutilizadas as features Cauchy físicas phi_j(u)=sqrt(u)u^j,
o quociente quiral completado Q e seu valor central Q(0)=-1.

Pins, fontes, métricas, amplitudes, fases, completion e normalizações ficam
inalterados. O operador consultado permanece em
`bfeb10fd2425400fa38139903d12bf0599f02e53`. As alterações preexistentes
no operador, em `momentos` e nas demais worktrees foram preservadas.

## B — O que foi demonstrado agora

### B1. Projeção linear no atlas primo original

Para qualquer estado X no carrier primo e qualquer atlas finito S:

    P_S X = sum_(p in S) single_p(<psi_p,X> psi_p^vee).

`primeProjection` é um mapa real-linear efetivo. Foram provados zero,
coordenadas, readouts preservados, autoadjunticidade, idempotência e
compatibilidade de atlas S contido em T, nas duas ordens de composição.
A construção não exige `realizesOn` nem `PosDef` dos momentos.

`prime_projection_polarized_pythagoras` demonstra, para X,Y independentes:

    <X,Y> = <P_S X,P_S Y> + <X-P_S X,Y-P_S Y>.

Os dois cruzamentos ativo/residual são demonstrados nulos separadamente.
`prime_projection_recovers_fixed_realization` recupera o estado antigo de
P09 quando a hipótese legítima de realização dos readouts fixos é satisfeita.
Assim o resultado anterior permanece válido em sua fibra afim.

### B2. Análise da fonte e cauda do atlas

`primeAnalysis S = P_S o T` reutiliza T. Seu pareamento é exatamente:

    <A_S X,A_S Y> = sum_(p in S) p/(p-1) <profile_p,X><profile_p,Y>.

`prime_analysis_synthesis` e `prime_analysis_all_crosses` conservam os dois
inputs e todos os produtos mistos em dimensões finitas independentes.
`prime_analysis_three_term_polarization` mantém a cauda original:

    <X,Y> = complementKernel(X,Y) + <A_S X,A_S Y>
           + <TX-A_S X,TY-A_S Y>.

Não se identifica `complementKernel` com o Green completado. O bound 11/12
vale para qualquer S, mas no domínio G_pre original, não na métrica Cauchy.

### B3. Duas quadraturas e forma assinada completa

`SignedReadoutSplit.lean` usa a duplicação real já existente, conserva sua
rotação J e reconstrói o produto complexo por `pack_inner`.
`complete_signed_readout_split` demonstra que aplicar a MESMA projeção às
duas pernas produz:

    <I,I'> - <R,R'>
      = [<PI,PI'> - <PR,PR'>]
        + [<(1-P)I,(1-P)I'> - <(1-P)R,(1-P)R'>].

As duas parcelas continuam assinadas. Nenhum dos resíduos foi apagado e não
se identificou a projeção com a operação de retorno. O enunciado é uma
identidade no carrier primo; não postula uma isometria da fonte Cauchy até ele.

### B4. Porta Mellin da mesma síntese física finita

`MellinPrimeReadout.lean` começa pela soma das features CONTÍNUAS originais,
com coeficientes c de suporte finito:

    F_c(u) = sum_j c_j sqrt(u)u^j
           = sqrt(u)[c_0 + u D_c(u)],
    D_c(u) = sum_(j<N) c_(j+1) u^j.

`original_continuous_with_trace` prova a reconstrução. O dado c_0 permanece
separado: ele é o termo constante depois de retirar a meia-densidade,
**não F_c(0)**. `original_continuous_zero` prova F_c(0)=0 para todo c.
Para u>0, `mellin_tail_from_original_source` calcula:

    D_c(u) = [F_c(u)/sqrt(u)-c_0]/u.

Somente depois dessa síntese completa vem o readout exato:

    integral_(0,1/p) D_c(u) du
      = sum_j c_j nativeUnitMassTowerProfile(p,1,j)
      = <profile_p, finiteTowerSynthesis(c)>.

`mellin_integral_prime_readout` identifica a mesma integral com a observação
prima de T. A correspondência de coeficientes ganhou uma fórmula integral
na fonte original; não foi inferida só porque ambos os índices são naturais.
Isso não identifica profundidade carry, endereço material e ordem de jet,
nem demonstra entrelaçamento dos respectivos geradores.

`original_complex_two_quadratures` demonstra a reconstrução dos coeficientes
complexos COMO IGUALDADE DE VETORES contínuos. Os teoremas `_toLp` levam as
somas às features L² originais depois da síntese, mantendo as duas quadraturas.

O domínio demonstrado é o das somas finitas parametrizadas. Não se afirmou
extensão limitada ao L² completo, isometria de `finiteTowerSynthesis`, nem
igualdade do kernel de energia com a Hankel canônica.

### B5. Defeito de kernel calculado, em vez de normalização

Defina K_S(i,j)=<A_S e_i,A_S e_j>, com e_j a base ORIGINAL da torre, e

    Delta_S(i,j) = 1/(i+j+2) - K_S(i,j).

`prime_column_kernel_formula` calcula K_S pelos perfis nativos.
`cauchy_prime_pairing_split` compara o resultado com o pareamento das features
Cauchy originais, sem escolher novos vetores a partir dos momentos.

`complete_chiral_kernel_prime_split` transporta essa diferença para CADA
entrada do kernel quiral radial original, mantendo seu quociente Q completado:

    G_(k;ij) = (k+1) K_S(i,j) [1-conj(Q_i)Q_j]
              +(k+1) Delta_S(i,j) [1-conj(Q_i)Q_j].

Vale para todos i,j, não apenas na diagonal. O fator Q preserva completion,
retorno e cruzamentos. Esta é a matriz de defeito do multiplicador Cauchy
original; não se troca sua normalização pela do kernel projetivo da PR #89.

Como K_S(0,j)=0, Delta_S(0,0)=1/2 para TODO atlas S.
`complete_chiral_first_source_defect` mostra que, nessa porta específica,
a primeira fonte radial fica inteiramente no defeito retido.

## C — O que foi refutado e alcance dos NO-GOs

### C1. A leitura prima isolada não é toda a informação do carrier

`prime_contraction_zero_level` prova T e_0=0, embora e_0 seja não nulo.
`zero_level_complement_energy` prova que a energia unitária permanece no
complemento existente. Esse eixo não é uma redundância de norma zero.
Não se afirma que toda fonte completada tenha componente nesse eixo; trata-se
do domínio anunciado do mapa, e não de uma identificação física presumida.

Os canários e_1,e_2 na câmera 2 preservam o cruzamento:

    Gram ativo = [[1/2,1/8],[1/8,1/32]].

### C2. A porta Mellin literal não é uma extração ortogonal na métrica Cauchy

A primeira feature não constante tem ||phi_1||²=1/4, enquanto
K_{ {2} }(1,1)=1/2. Logo Delta_{ {2} }(1,1)=-1/4.
`no_original_cauchy_positive_loss` prova que nenhum canal de norma positiva
pode satisfazer

    ||phi_1||² = K_{ {2} }(1,1) + ||D||².

A contração de T não é contradita: ela usa a norma dos COEFICIENTES na torre,
na qual ||e_1||²=1. O mapa de coeficientes Cauchy -> torre não foi isométrico.
Adicionar um canal positivo de trace não corrige energia que já excede a
norma física. Não se ajustaram pesos para eliminar o defeito negativo.

Este NO-GO refuta a leitura Mellin/prime literal como um porto ortogonal
positivo nessa métrica e nesses eixos. Não refuta toda realização geométrica.

### C3. A análise prima T não é o retorno quiral bruto por portos isométricos

`native_return_ratio_limit` usa somente a continuidade da fonte e Q(0)=-1:

    ||Q(z_(k,j))||² -> 1,  para todo endereço j fixo.

Portanto, para qualquer rho<1, eventualmente a energia retornada excede
rho vezes a energia incidente da MESMA coluna Cauchy original.
T e A_S possuem a margem fixa 11/12. Assim, mesmo com portos isométricos
DISTINTOS para incidência e retorno, não pode valer eventualmente:

    W(R_(k,j)) = T(L(I_(k,j))).

`no_eventual_isometric_finite_prime_return` exclui também substituir T por
A_{S(k)}, com qualquer escolha ou crescimento do atlas. Aumentar o número de
câmeras não corrige essa identificação específica. Isso não exclui uma
coligação enriquecida com fluxo e defeitos, nem mapas em domínios nativos
mais regulares que não imponham essa igualdade de normas separadas.

## D — Campanha VM, validação e o que permanece aberto

### O material indicado ajuda como regressão

A cópia autenticada do README no GitHub foi conferida contra a existente em
`/home/thlinux/momentos`. O caminho histórico `~/native-jet-vm-20260930` não
existe hoje; os checkpoints relevantes estão dentro do repositório.
Nenhuma campanha, instalação, cálculo de milhares de momentos ou espectro
novo foi iniciado.

`audit_vm_campaign.py` conferiu os três hashes de fontes arquivadas do
`vm-n40-reference/run.json`, seus 80 momentos e os 64 `canonical_h` salvos em
`stage_A/moments.csv`. A comparação encontrou 313 dígitos relativos comuns,
com pior erro aproximadamente 1.394e-314 no índice 63. É verificação numérica
de arquivos já existentes, não intervalo certificado nem prova all-order.

SHA256 do run: `9267df79f0b6c38508d790a14aca6e79bad16cc009518b4a8a881a13c07006ad`.
SHA256 do CSV: `05734f8898aae995d77360c79e60521855181fede3f7f2a46c6b1bc1bc8e1833`.

`moments`/`canonical_h` correspondem à sequência canônica; `raw_moments` e
`f_coefficients` têm outro papel. A recorrência monônica da campanha verifica
sinais antes das raízes/normalizações; não os deriva da geometria.
Os arquivos não preservam os vetores I/R nem readouts do atlas primo.
O produto B_N experimental de bordo também não possui ali igualdade
geométrica demonstrada. Os dados ajudam a escolher/conferir coeficientes de
inputs físicos existentes, mas não fornecem o intertwiner ausente.

### Validação

**Validação concluída:** 67 teoremas novos e 12 definições, totalizando
79 raízes públicas; 5731 dependências de tipos/corpos auditadas; 18 comandos
com exit 0. Nenhuma definição da sequência canônica entra na construção
verificada dos novos resultados.

Os resultados completos são registrados em `evidence/validation.json`,
`evidence/lean-Audit.log`, `evidence/vm-campaign-audit.json` e
`evidence/source-provenance.json`. A reprodução na branch desta entrega, no ambiente do servidor registrado, usa:

```bash
cd research/source-dependent-prime-readouts
python3 validate.py
```

Os módulos novos são compilados explicitamente com `warningAsError=true`.
São executados `lake build --wfail`, auditorias Foundation/Geometry/Analysis,
verificação de preservação da base e de fontes/pins/arquivos preexistentes.
A auditoria nova percorre tipos e corpos transitivos, incluindo privados,
permitindo somente propext, Classical.choice e Quot.sound. Ela também rejeita
construções dependentes da própria sequência de momentos canônicos ou dos
consumidores condicionais de positividade.

A fonte não foi alterada para satisfazer os instrumentos. A forma positiva
no carrier primo não foi anunciada como a Hankel nativa. Não se provou a lei
all-order de sinal nem a extensão da porta Mellin ao domínio completo.

## E — Próximo passo mínimo

A projeção dependente do input foi construída; a tentativa literal de usá-la
como energia/retorno Cauchy foi testada e obstruída. Não repetir essa
identificação nem recertificar o pivô finito theta.

O próximo teste concreto é a **admissibilidade da porta Mellin com o dado de
bordo retido no domínio nativo**. Uma identidade em polinômios finitos não é
uma aplicação limitada sobre o L² inteiro. Investigar primeiro se tal extensão
é limitada/fechável, e em qual domínio ORIGINAL as subtrações de bordo fazem
sentido, antes de transportar Grams ou passar a uma síntese infinita.

Um teste analítico curto, ainda NÃO formalizado nesta entrega, usa
D_n(u)=(1-u)^n e F_n(u)=u^(3/2)(1-u)^n, ambos derivados de coeficientes finitos
e com trace zero. As fórmulas elementares previstas são:

    readout_p(F_n) = [1-(1-1/p)^(n+1)]/(n+1),
    ||F_n||² = 6/[(2n+1)(2n+2)(2n+3)(2n+4)].

Elas sugerem que o funcional não é limitado na norma L² simples. Esse é um
alvo verificável, não um novo teorema anunciado. Uma eventual obstrução de
extensão seria específica dessa porta nesse domínio; não autorizaria mudar
a métrica nem descartar os bordos. O transporte completo pode exigir a
regularidade que a própria fonte e suas condições de bordo já fornecem.

Em paralelo, `complete_chiral_kernel_prime_split` fornece o defeito exato
que qualquer costura positiva dessa rota terá de controlar, com todos os
cruzamentos e o mesmo retorno. O sinal não foi convertido em uma condição
de funcionamento nem recebido como hipótese disfarçada.

**Fim do relatório.**
