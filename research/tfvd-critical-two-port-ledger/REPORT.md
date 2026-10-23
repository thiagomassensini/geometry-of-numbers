# Ledger TFVD de dois ports na direção crítica fixa

**Classificação: PARTIAL.** A direção fixa da PR #64 foi transportada ao produtor TFVD completo, com igualdade vetorial, dois argumentos independentes, caudas, completion e cruzamentos. A soma do fluxo de cabeça com sua correção converge ao pivô exato, sem hipótese de seu sinal. Foi provada uma obstrução condicional à convergência separada dessas parcelas; o diagnóstico da fonte original mostra mudança de sinal das cabeças e cancelamentos grandes. Nenhum sinal canônico all-order novo foi demonstrado.

Branch: `agent/tfvd-critical-two-port-ledger`.
Base: `adb6fdce56d626b9ecf22b013530c8027c3240c1`, cabeça da PR #64. A entrega é empilhada em draft, sem merge automático. PRs anteriores, `main`, pins e fontes históricas permanecem preservados.

Fonte física reutilizada: `carry-self-adjoint-operator` em `bfeb10fd2425400fa38139903d12bf0599f02e53`, sem edições. Os dois arquivos não rastreados do operador, o resíduo da PR #51 e os worktrees preexistentes foram preservados.

## A — O que já estava demonstrado

As notas em `/home/thlinux/Downloads/IMPORTANTE/POSITIVIDADE` apontaram a carta física de endpoint e o segundo port TFVD. Sua conferência anterior mostrou que essas peças já existiam no código:

- `physicalEndpointJetInput_decode`, `physicalEndpointJetInput_wholeSource`, de `NativePhysicalEndpointEncoder.lean`: a reconstrução polinomial de endpoint fornece a mesma síntese das duas pernas.
- `tfvdMaterialWholeSource_canonical`, `tfvdCanonicalResponse_regular_denominators`, `tfvdStateHeadTail_responseDefect`, de `NativePhysicalTfvdSecondPort.lean`: produtor completo, regularidade e determinante das duas caudas.
- `twoPort_signed_form`, de `NativePhysicalTwoPortChart.lean`: forma original em duas entradas, sem uma nova métrica.
- `nativeSourceProjectiveBoundaryJetSynthesis_energy_tendsto`: limite do balanço físico original.
- `native_inverseSchur_boundary_energy`, da PR #41, recuperada no commit imutável `ee56930a2c30456cfbd214a29bb31b12d3977204`: a direção crítica tem energia `4p` sob apenas `IsUnit A`.
- `returnExcess_tendsto`, da PR #64: o excesso do retorno na direção fixa converge a `−E/2`, sem receber seu sinal.
- `finite_eventually_admissible`, da PR #63: domínio e denominadores completos são simultaneamente regulares em cada suporte fixo.

Não se reabriu a identificação Gamma–Wronskiano global já refutada. A fonte TFVD completada, seu chart e seu fator Xi permanecem os mesmos. A revisão isolada `SecondPortPairingChange.lean` foi incorporada e estendida, com autoria/proveniência desta mesma investigação; não houve novo port de módulos históricos.

## B — O que foi demonstrado agora

Todos os nomes novos pertencem ao namespace `CarryTfvdCritical`.

### 1. O mesmo input, com a escala e a fase originais

Seja `x : Fin (2*n) → ℂ` uma coordenada de fronteira **fixa enquanto k varia**. Definimos apenas sua reconstrução existente:

$$
v_k=\operatorname{decodedEndpointCoefficients}(2n,k,x).
$$

Os estados TFVD de cutoff `M` são os `canonicalC3BracketTfvdCompletionState` nos nós radiais originais. Se `Θ_G` é a resposta completa desses estados e `Θ_H` a expressão da cabeça já existente, escrevemos

$$
s_G=\Theta_G\odot v_k,\qquad s_H=\Theta_H\odot v_k,\qquad e=s_G-s_H.
$$

`fullSource_eq_original` prova, na seção física regular,

$$
P(v_k,s_G)=\operatorname{nativeSourceProjectiveBoundaryJetSynthesis}(n,k,x).
$$

É uma igualdade do **par vetorial completo**, antes da forma assinada. Não se divide cada coordenada por uma amplitude ajustada, nem se aplica a amplitude uma segunda vez. A fase e os fatoriais já estão na carta original.

`fullSource_eventually_eq_original` prova que a mesma seção eventual de `k` funciona para **todos os cutoffs TFVD exatos M e todos os inputs nessa dimensão**. Isso se deve a manter as caudas exatas. Não é uma afirmação de que as cabeças sejam iguais entre cutoffs.

### 2. Ledger em dois argumentos independentes

Use a notação `C_N(i,j)=1/(i+j+2)` para o Gram Cauchy físico, distinguindo-o da Hankel canônica, e `K=k+1`. A síntese `P(v,s)` é `twoPortSynthesis`, no carrier original. Sua forma é

$$
\Omega(P(v,s),P(w,t))=\frac{iK}{2}(s^*C_Nw-v^*C_Nt).
$$

Em `TwoPortCorrection.lean`, `secondPort_pairing_change` prova

$$
\Omega(P(v,s+e),P(w,t+f))-\Omega(P(v,s),P(w,t))
=\frac{iK}{2}(e^*C_Nw-v^*C_Nf).
$$

Não há termo erro–erro nessa diferença quando o primeiro port está fixo. Isso não apaga o canal diagonal como vetor: ambos os cruzamentos permanecem.

`full_head_polarized_ledger`, em `FixedSourceTfvd.lean`, aplica a identidade a inputs `x,y` e cutoffs TFVD `M,L` independentes. Nenhuma quadratura é substituída por uma norma positiva auxiliar.

Somente depois, `twoPort_real_self` e `full_head_real_ledger` extraem a diagonal real:

$$
\boxed{\Omega_G(x,x)=A_{M,k}(x)+B_{M,k}(x),}
$$

$$
A_{M,k}=K\operatorname{Im}(v_k^*C_Ns_H),\qquad
B_{M,k}=K\operatorname{Im}(v_k^*C_Ne).
$$

São `headFlux` e `correctionFlux`, readouts da forma antiga. Não são novos produtos internos.

### 3. O determinante conjunto e uma identidade sem dividir pela cabeça

`errorSecond_determinant` aplica o teorema existente da resposta aos mesmos coeficientes físicos:

$$
e_j=i\,\frac{T_{H,j}L_{T,j}-L_{H,j}T_{T,j}}{T_{H,j}(T_{H,j}+T_{T,j})}\,v_{k,j}.
$$

A identidade exige os denominadores completos e `T_H≠0`. `exact_ratio_denominators_eventually` descarrega os denominadores **completos**, para todos os cutoffs exatos. Não descarrega a não anulação da cabeça.

Para não resolver uma singularidade de cabeça pela inversão total de Lean, `tfvd_head_cross_residual` prova separadamente

$$
\boxed{T\{T_H[\Theta_G-B_{\Xi,Q}]-iL_H\}
=i(T_HL_T-L_HT_T),}
$$

$$
B_{\Xi,Q}=\Xi^c/\Xi+iQ'/Q,\qquad T=T_H+T_T.
$$

Essa relação não divide por `T_H` e continua válida se a cabeça zerar; ainda preserva as condições de regularidade de Xi, chart e valor completo. Não se confunde esse residual multiplicado com a diferença de quocientes em um zero da cabeça.

### 4. O pivô recuperado para qualquer schedule de cutoff exato

`jet_form_re_eq_excess` conserva a normalização da PR #64: `Ω=−returnExcess/2`. `original_flux_ledger_eventually` identifica a soma com essa forma original.

`total_flux_tendsto` permite uma função arbitrária `cutoff : ℕ → ℕ`:

$$
A_{M(k),k}(x)+B_{M(k),k}(x)\longrightarrow E_{2n}(x)/4.
$$

Com `x=criticalCoordinates s n`, fixado pelos momentos canônicos originais e **não recalculado com a cabeça**, `critical_total_flux_tendsto` obtém

$$
\boxed{A_{M(k),k}(x)+B_{M(k),k}(x)\longrightarrow p_{s,n}.}
$$

A hipótese é somente inversibilidade do prefixo antigo, como na PR #41. Não se assume `p≥0` ou `A.PosDef`.

A liberdade de schedule vem da identidade com caudas exatas para cada M. Ela não autoriza trocar limites de aproximações numéricas, nem afirma uniformidade de seus erros quando M,n,k crescem.

### 5. Uma estimativa física, com sua limitação explícita

`correctionFlux_abs_bound` fornece

$$
|B_{M,k}|\le\|I_k(v_k)\|\,\|I_k(e)\|,
$$

na métrica Cauchy original. É consequência de Cauchy–Schwarz, não uma nova coerção. Um erro pequeno não basta quando o vetor com que cruza cresce. Nenhum sinal all-order foi extraído desse orçamento absoluto.

## C — O que a tentativa mostrou sobre separação de cabeça e correção

Em `HeadCancellation.lean`, tome o primeiro par `x₀=![1,0]`. `first_even_material` recupera exatamente `v_k=![1,0]`. Para a resposta central da cabeça canônica

$$
\beta_M=\operatorname{Im}\Theta^H_M(0),
$$

`first_even_head_formula` e `first_even_head_normalized` provam

$$
A_{M,k}(x_0)/K=\operatorname{Im}\Theta^H_M(i/K)/2.
$$

**Sob a hipótese explícita** de continuidade dessa resposta da cabeça no centro, `first_even_head_scaled_tendsto` e `first_even_correction_scaled_tendsto` dão

$$
\boxed{A_{M,k}/K\to\beta_M/2,\qquad B_{M,k}/K\to-\beta_M/2.}
$$

A soma não recebe hipótese de sinal: seu limite finito vem da fonte original.

`fixed_head_no_finite_limit` e `fixed_correction_no_finite_limit` provam que, **se também β_M≠0**, nenhuma das duas parcelas possui limite finito separado. Portanto uma estratégia de tratar a correção como erro absoluto desaparecendo, mantendo esse cutoff fixo, falha nessas condições.

O alcance é condicional e específico dessa separação. Não foi provada nesta entrega a continuidade para todo cutoff, nem certificada em Lean a não anulação de β_M nos cutoffs numéricos abaixo. Não é anunciado um no-go incondicional da síntese completa.

`Regression.lean` conserva também a fase do primeiro ímpar e o segundo perfil par:

$$
v_k^{\rm odd}=(iK,-iK),\qquad
v_k^{\rm even,2}=(a-K^2/2,K^2,-K^2/2,0)
$$

para os inputs `![0,1]` e `![a,0,-1,0]`, respectivamente. O parâmetro a é arbitrário nessa prova; os momentos não definem o carrier.

### Diagnóstico da fonte original, sem theta ou zeros na avaliação

`experiment.py` utiliza a câmera C3 literal:

$$
T_H(s)=1+\sum_{m=1}^{M}[(3m-1)^{-s}-2(3m)^{-s}+(3m+1)^{-s}],\quad L_H=-T_H',
$$

mais os fatores Xi/chart originais. A cauda completa é aproximada por expansão de Taylor dos brackets e Euler–Maclaurin das somas de potências, com 70 casas, dois prefixos independentes J=128 e J=256, dez termos Taylor e oito termos EM. Não se chama zeta, integral theta, tabela de zeros ou alturas. Não se impõe que a resposta no centro seja zero.

Essas avaliações **não são intervalos certificados**. Os momentos decimais anteriormente fornecidos são usados somente para escolher a direção numérica aproximada `a=−h₁/h₀` e comparar limites de baixa ordem; não entram no produtor da resposta.

A parte imaginária central da cabeça, observada numericamente, é:

| M | β_M aproximado |
|---:|---:|
| 0 | `+0,0867471257143` |
| 1 | `+0,00570242507344` |
| 2 | `−0,000908218082574` |
| 4 | `−0,00218052311208` |
| 16 | `−0,000890470565696` |
| 64 | `−0,000194156298255` |

Logo não há indicação numérica de uma orientação uniforme das cabeças. A resposta completa no centro, sem forçar cancelamento, foi aproximadamente `−6,39×10⁻⁴¹` e `−1,49×10⁻⁴⁶` nas duas avaliações da cauda. A simetria exata da fonte não é substituída por esses números.

Com K=2048 e M=2, a avaliação com J=256 fornece:

| Direção | Cabeça A | Correção B | Soma completa |
|---|---:|---:|---:|
| Primeiro par | `−0,89247944` | `+0,91558443` | `0,0231049931066` |
| Primeiro ímpar | `−650149,94836965` | `+650149,94840682` | `3,71725991134×10⁻⁵` |
| Segundo par | `−2,72688007028×10¹¹` | `+2,72688007028×10¹¹` | `8,43685840774×10⁻⁸` |

Os números arredondados da tabela não devem ser subtraídos para recuperar a soma; os valores de maior precisão estão em `evidence/experiment.json`. A maior diferença observada entre os fluxos completos dos dois prefixos foi aproximadamente `1,92×10⁻²⁶`, sem certificação intervalar desse endpoint.

Foram conservados todos os pares do Gram e verificadas as identidades de dois ports e do determinante. Os coeficientes dominantes esperados, testados como diagnósticos no primeiro ímpar e segundo par, são `β_M/12` e `β_M/120` nas escalas K³ e K⁵. Essas duas leis assintóticas adicionais não receberam prova Lean nesta entrega. O resultado formal da escala separada é o do primeiro par.

## D — O que permanece aberto

1. Não se demonstrou um sinal all-order do fluxo completo ou dos pivôs canônicos. A igualdade do total com o pivô localiza o problema; não constitui uma causa independente de seu sinal.
2. Não há um contraexemplo canônico negativo. Uma cabeça numericamente negativa com correção positiva não é a forma completada inteira.
3. As hipóteses analíticas e a constante central do no-go condicional da cabeça não foram descarregadas para os cutoffs concretos. Os valores de β_M acima são diagnósticos, não premissas Lean.
4. O residual sem divisão pela cabeça não resolve o sinal por si só. Ele conserva os dois termos de cauda e suas interações, incluindo chart e completion.
5. As identidades não identificam o Gamma resolvente com o Wronskiano canônico nem alteram as obstruções anteriores. Tampouco constroem uma nova Jacobi ou operador de alturas.

## E — Próximo passo mínimo

O teste mostrou que a correção não deve ser tratada automaticamente como uma margem pequena em cutoff TFVD fixo. O passo seguinte é extrair o primeiro termo **conjunto** não cancelado do produtor completo, conservando a identidade multiplicada do determinante antes de dividir ou estimar módulos.

Há duas obrigações distintas:

- Para tornar incondicional a obstrução da cabeça no primeiro par: provar a continuidade do head canônico e certificar `β_2≠0` pela expressão finita original. Isso encerraria essa estratégia de separação, mas não provaria positividade da soma.
- Para avançar o sinal canônico: obter uma identidade de fluxo ou desigualdade da **soma recombinada**, produzida pelas relações TFVD/Green originais, que restrinja o primeiro coeficiente sobrevivente sem receber como margem o pivô que se deseja provar. Usar diretamente o determinante e o mesmo input x, evitando majorar separadamente parcelas que o ledger obriga a cancelar.

Não se propõe ajustar a constante central da resposta, renormalizar uma cabeça para fazê-la par ou trocar a fonte. Qualquer reorganização do cancelamento deve ser uma igualdade da mesma soma original. O sucesso estrutural ainda exige uma restrição de sinal independente, e não apenas reescrever `p≥0` como um fluxo não negativo.

## Validação e reprodução

Há 26 teoremas e 11 definições públicas novas. `generate_audit.py` inventaria as 37 raízes e audita transitivamente tipos e corpos. Bloqueia consumidores posteriores H6/K6/H7, gates de contratividade relevantes e os sinais conhecidos de h₀ e h₁. A auditoria preliminar passou com apenas `propext`, `Classical.choice`, `Quot.sound`; o maior fecho de dependências tem 5.985 constantes.

Sem novos axiomas matemáticos ou escapes de confiança. Os seis módulos de pesquisa, incluindo regressão e auditoria, são compilados explicitamente com `warningAsError=true`. O build raiz sozinho não inclui automaticamente estes módulos.

Na pilha de pesquisa já compilada da PR #64:

```bash
cd /home/thlinux/geometry-of-numbers
python3 research/tfvd-critical-two-port-ledger/validate.py
```

O script executa 16 verificações: geração da auditoria, seis módulos, diagnósticos, builds focado e raiz com `lake build --wfail`, auditorias Foundation/Geometry/Analysis, regressão das doze fontes, preservação dos arquivos históricos e `diff --check`. Usa as mesmas dependências e recuperações imutáveis da PR #64; não é um bootstrap integral dos caches históricos numa máquina vazia.

**Execução concluída: 16/16 verificações passaram.** Os seis módulos novos, os diagnósticos, os builds com `--wfail`, as três auditorias e a regressão das doze fontes concluíram com código zero. A auditoria transitiva das 37 raízes permitiu somente os três axiomas fundacionais declarados.

Resultados efetivos, comandos, tempos, hashes e referências protegidas são registrados em `evidence/checks.json`, `evidence/kernel-Audit.log`, `evidence/preflight.json` e `evidence/source-sha256.json`.
