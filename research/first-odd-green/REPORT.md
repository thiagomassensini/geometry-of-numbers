# Primeiro jet ímpar: portas Green originais e cancelamento quadrático

Classificação: **PARTIAL** para a ponte positiva global. **Alvo local demonstrado:** porta de `e₁`, todos os cruzamentos com `e₀` e primeira diferença normalizada ímpar original.

Base: `365d91c60d49740a4c31153e90d620f424eec8fe` (PR #84, draft). Branch: `agent/first-odd-green`. Base de revisão: `agent/finite-green-crossing`; não presumir que PRs anteriores estejam no main. Nenhuma alteração em módulos históricos, métricas, fontes ou pins. Sem merge automático.

## A — O que já estava demonstrado

A PR #41 separou ortogonalização polinomial algébrica e positividade. O residual de Schur não recebe sinal por ter sido ortogonalizado. Essa distinção permanece.

A PR #81 construiu `physicalJet` e provou `physical_jet_original`, `common_jet_pairing_tendsto` e `common_odd_jets`: os jets físicos originais, após refinamento isométrico comum, recuperam o kernel canônico assinado em duas variáveis. Isso não é uma Gram positiva de Hilbert.

A PR #82 provou `refined_source_green_split`, `reconstructed_residual_pairing_zero` e `physical_form_four_sectors`. O setor residual–residual é zero porque as duas pernas são iguais; o residual físico não é descartado. Os dois cruzamentos mistos permanecem.

A PR #83 manteve as portas média/contraste e isolou o orçamento Green. A PR #84 extraiu a porta original de `e₀`, incluindo `residual_numerator_initial`, `reconstructed_residual_initial`, `initial_mixed_pairing` e `bulk_energy_limit`. Em `e₀`, as duas parcelas separadas possuem limites finitos.

H6, K6 e a realização finita de doze fontes são resultados finitos anteriores. Não fornecem por extrapolação o sinal de um pivô arbitrário nem justificam uma Gram infinita positiva. O presente trabalho não modifica esses certificados.

## B — Identidades desta continuação

Escrevemos κ = k+1, δₖ = i/κ e zⱼ = (j+1)δₖ. `k` é o índice radial, não profundidade vertical Carry. η é o parâmetro do Green físico; não é o quociente quiral nem uma constante ajustada. Todos os resultados analíticos abaixo conservam 0 < η < 1.

A resposta é a original `nativeResponse = -F′/(2F)`. As colunas antigas são φⱼ(x)=√x·xʲ, no fechamento físico Cauchy, com o mesmo produto interno. Definimos αₖ=√(2κ), ΔRⱼ=R(zⱼ₊₁)-R(zⱼ). As novas abreviações `basisInput` e `oddInput` são apenas coeficientes finitos da síntese linear já existente.

A forma antiga é Φ(u,v) = ½(〈u⁺,v⁺〉−〈u⁻,v⁻〉). Ela é assinada. Uma parcela Φ(B,B) negativa não é uma norma hilbertiana negativa: cada norma das duas pernas continua não negativa. Os sinais abaixo dizem respeito a esse balanço, nunca a uma alteração da métrica.

### A porta sucessora depende do bordo

O stencil original tem coeficiente zero em índice zero. Logo:

\[
 B_η e_1=-2e_1+η e_2,
 \qquad N_η e_1=-η A\mathcal E_1,
 \qquad \mathcal E_j=α_k\Delta R_j(φ_{j+1},φ_{j+1}).
\]

Não se deve inserir η⁻¹e₀ no bulk. Os termos do bordo e do residual cancelam-se em conjunto. A porta reconstruída é

\[
 Q_η=-η^2G_η^2φ_3,
 \qquad \widehat E_1=α_k\Delta R_1(Q_η,Q_η).
\]

A porta anterior é Pη=ηGη²(2φ₁−ηφ₂). Os perfis físicos são

\[
 P_η(x)=\frac{η(2-ηx)}{(1-ηx)^2}\sqrt{x}x,
 \qquad Q_η(x)=-\frac{η^2}{(1-ηx)^2}\sqrt{x}x^3.
\]

Esses vetores são imagens pelo resolvente antigo. Não são definidos de momentos ou de um pareamento desejado.

### Quatro cruzamentos, antes da leitura real

Para i,j∈{0,1}, com P₀=Pη e P₁=Qη:

\[
 \Phi(\widehat B_i,\widehat E_j)
 =-iκ\Delta R_j\langle φ_i,P_j\rangle.
\]

A identidade é complexa, ordenada e finita. As hipóteses são somente o domínio de η e a não anulação original de F e E⁺ nos três nós 0,1,2; não há hipótese de positividade Hankel.

O primeiro jet ímpar não é o endereço material `e₁`. Sua fonte é exatamente

\[
 \mathcal J_1(k)=δ_k^{-1}(S_1-S_0)
 =\widehat B_{\rm odd}+\widehat E_{\rm odd}.
\]

As partes são a mesma diferença normalizada das reconstruções antigas. As igualdades `odd_source_original`, `odd_residual_original` e `odd_bulk_original` verificam o transporte do mesmo coeficiente `oddInput`; `first_odd_jet_difference` verifica o fatorial e a fase do jet original. Para Oⱼ=〈φ₁−φ₀,Pⱼ〉:

\[
 \Phi(\widehat B_{\rm odd},\widehat E_{\rm odd})
 =-iκ^3(\Delta R_1O_1-\Delta R_0O_0).
\]

Antes dessa redução, `odd_mixed_four_crossings` conserva explicitamente os quatro termos (11−10−01+00) e o fator conjugado δ̄⁻¹δ⁻¹=κ². O setor EE só é anulado após a identificação vetorial das pernas iguais.

### Um coeficiente positivo da fonte, anterior aos momentos

A diferença de overlaps é

\[
 A_η=\langle φ_1-φ_0,Q_η-P_η\rangle
 =\int_0^1\frac{ηx^2(1-x)(2-ηx+ηx^2)}{(1-ηx)^2}\,dx
 \geq\frac{η}{12}>0.
\]

A igualdade provém dos perfis físicos originais no mesmo L². A desigualdade segue ponto a ponto pela comparação com η(x²−x³). Nenhum momento, pivô ou certificado de positividade define Aη.

### Escala nova: as partes separadas divergem

A regularidade do germe original fornece κΔRⱼ→ih₀ para cada endereço fixo. Portanto:

\[
 \frac{\Re\Phi(\widehat B_{\rm odd},\widehat E_{\rm odd})}{κ^2}
 \longrightarrow h_0A_η,
 \qquad
 \frac{\Re\Phi(\widehat B_{\rm odd},\widehat B_{\rm odd})}{κ^2}
 \longrightarrow-2h_0A_η.
\]

Entretanto, o total completo obedece

\[
 \Re\Phi(\mathcal J_1,\mathcal J_1)=\Re\Phi(\widehat B_{\rm odd},\widehat B_{\rm odd})
 +2\Re\Phi(\widehat B_{\rm odd},\widehat E_{\rm odd})\longrightarrow h_1.
\]

O limite total reutiliza o teorema canônico de duas variáveis e a isometria, sem substituir o kernel. A hipótese antiga h₀>0 dá sinais eventuais opostos para as parcelas. Compensação estrita do total é apresentada separadamente sob h₁>0. Isso não prova h₁>0 pela nova decomposição. O certificado antigo de h₀ usa a rota analítica theta/cosseno; não anunciamos uma nova prova geométrica desse sinal.

## C — O que a continuação exclui

1. Aplicar a `e₁` um stencil interior que desrespeita o coeficiente zero imposto pelo bordo.
2. Identificar o endereço `e₁` com a primeira ordem ímpar sem a diferença δ⁻¹(e₁−e₀).
3. Extrapolar os limites finitos separados de `e₀` para o primeiro jet ímpar. `odd_mixed_no_finite_limit` e `odd_bulk_no_finite_limit` refutam formalmente a existência desses limites para 0<η<1 e h₀>0, pela unicidade do limite normalizado. O total finito depende dos dois cruzamentos.
4. Interpretar EE=0 como vetor residual nulo ou como autorização para apagar BE e EB.
5. Deduzir positividade canônica all-order de Aη>0: esse coeficiente controla a parte dominante que se cancela, não o sinal do próximo residual finito.

Nenhum desses pontos é uma impossibilidade geral da geometria Carry.

## D — Resultados Lean e validação

São 56 teoremas e 12 definições novas, em cinco módulos separados. Todos os nomes abaixo estão no namespace `CarryFirstOddGreen`.

| Arquivo | Teoremas principais | Hipóteses relevantes |
| --- | --- | --- |
| `SuccessorPort.lean` | `successor_bulk`, `successor_residual_numerator`, `residual_basis_pair`, `reconstructed_successor` | Stencil/numerador algébricos sem sinal; para identificar pernas, não anulação original em nós adjacentes. |
| `FirstOddJet.lean` | `ordered_mixed_pairing`, `odd_source_original`, `odd_residual_original`, `odd_bulk_original`, `odd_mixed_four_crossings`, `odd_mixed_exact`, `odd_energy_three_sectors` | Para a reconstrução: 0<η<1; pareamentos: regularidade em 0,1,2. Fatorial, fase e cada cruzamento preservados. |
| `OddPortOverlap.lean` | `successor_port_toLp`, `odd_port_overlap`, `odd_density_lower`, `odd_coefficient_lower`, `odd_coefficient_pos` | 0≤η<1 para identificação e cota; η>0 para sinal estrito. Sem momentos como entradas. |
| `OddAsymptotics.lean` | `increment_basis_limit`, `odd_mixed_scaled_limit`, `odd_source_complex_limit`, `odd_source_limit`, `odd_bulk_scaled_limit` | Germe completado original, regularidade eventual descarregada e 0<η<1; sem certificado de sinal finito. |
| `OddSigns.lean` | `odd_eventual_mixed_positive`, `odd_eventual_bulk_negative`, `odd_mixed_no_finite_limit`, `odd_bulk_no_finite_limit`, `odd_eventual_compensation`, `canonical_odd_channel_signs` | Sinais das parcelas e NO-GOs usam h₀>0; compensação estrita usa separadamente h₁>0; apenas o último teorema insere o certificado antigo de h₀. |

A auditoria `Audit.lean` imprime os axiomas de todas as 68 raízes públicas e percorre transitivamente os tipos **e corpos**, incluindo constantes privadas:

| Grupo | Raízes | Dependências únicas de tipos/corpos | Restrição adicional |
| --- | ---: | ---: | --- |
| Construção da fonte | 48 | 5833 | Proíbe usar os momentos canônicos para definir os estados; proíbe certificados finitos posteriores. |
| Identificação/limites | 14 | 6024 | Permite a sequência original; proíbe certificados de sinal finito e polinômios theta. |
| Corolários de sinal | 6 | 5959 | Permite o certificado antigo de h₀; sem certificados H6/K6 e sem consumidores all-order proibidos. |
| União | 68 | 6104 | Somente `propext`, `Classical.choice` e `Quot.sound`. |

**PASS nos 16 comandos registrados em `evidence/validation.json`:** proveniência ancestral, geração da auditoria, build focado dos operadores antigos com `lake build --wfail`, compilação explícita dos cinco módulos novos e de `Audit.lean` com avisos tratados como erros, diagnóstico Python, `lake build --wfail` na raiz, auditorias Foundation/Geometry/Analysis, preservação da base e `git diff --check`.

Nenhum `sorry`, `admit`, `native_decide` ou axioma novo nas fontes. Os SHAs dos módulos nativos e dos dois arquivos preexistentes não rastreados no operador foram preservados. O build raiz não importa implicitamente os módulos de pesquisa: eles foram compilados e auditados explicitamente antes dele.

Reprodução no servidor canônico `llm`, em um checkout desta branch com as dependências e toolchain já preservadas:

```bash
cd /home/thlinux/geometry-of-numbers-first-odd-green/research/first-odd-green
mkdir -p evidence
python3 build_upstream.py > evidence/upstream-build.log 2>&1
python3 validate.py
```

`compile_module.sh` usa as fontes imutáveis dos ancestrais e a toolchain do repositório nativo. `record_provenance.py` compara cada fonte ancestral com o commit base, registra SHAs dos `.olean`, fontes originais, pins e estado dos PRs. PR #41 foi conferida como draft aberta, head `ee56930a2c30456cfbd214a29bb31b12d3977204`; permanece intacta.

O diagnóstico Python foi executado a 80 e 120 dígitos. Avalia F pela identidade downstream já provada com a característica xi; **não reexecuta a síntese material TFVD** e não lê zeros, alturas ou tabelas de momentos. Confere os quatro cruzamentos separadamente, a igualdade com o total, e as duas escalas. No C2, Aη≈0,40266654705909; h₁≈0,00003717259928527. Esses decimais são diagnóstico, não premissas Lean. O sinal e a cota de Aη acima são teoremas racionais/analíticos independentes desse teste.

Os comandos e saídas completas ficam em `evidence/`; `validation.json` inclui os hashes das fontes novas. Os 25 módulos ancestrais foram recompilados a partir das fontes base, sem alteração.

## E — Próxima obrigação mínima

O primeiro lema concreto a provar é, para todo j≥0,

\[
 N_ηe_{j+2}=η^{-1}\mathcal E_{j+1}-ηA\mathcal E_{j+2}.
\]

Ele deve ser derivado do stencil e dos bordos existentes, antes de identificar perfis. Então a porta reconstruída de endereço r≥2 terá a fórmula candidata αₖGη²(ΔRᵣ₋₁φᵣ−η²ΔRᵣφᵣ₊₂), cuja igualdade vetorial ainda não é teorema desta PR. Depois transportar essas portas para a próxima diferença normalizada, antes de tomar o pareamento. O primeiro teste crítico é a segunda direção par da PR #41: J₂−(h₁/h₀)J₀, com o fatorial 2 e a fase δ² do jet original. Sua forma limite deve conservar h₂−h₁²/h₀, sem receber o sinal desse pivô como hipótese. A primeira verificação deve ser o cancelamento exato dos coeficientes divergentes, com dois argumentos independentes.

O alvo de sinal global continua sendo o primeiro coeficiente finito que sobra na direção crítica ortogonalizada da PR #41, depois desses cancelamentos completos. Não basta provar o sinal de outro coeficiente dominante positivo. É necessária uma identidade ou desigualdade independente da fonte para esse residual, sem usar o sinal desejado para definir os vetores.

**Conclusão:** esta continuação demonstra a extração de `e₁` e a primeira diferença ímpar; a representação Gram positiva da sequência canônica em toda ordem permanece aberta.

FIM DO RELATÓRIO — FIRST_ODD_GREEN
