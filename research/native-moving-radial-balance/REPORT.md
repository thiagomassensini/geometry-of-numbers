# Fonte crítica móvel: transporte físico, derivada completa e orientação ímpar

Classificação: **PASS_STRUCTURAL para o transporte e a derivada da fonte móvel; PARTIAL para uma lei de sinal canônica em toda ordem.** Há também uma orientação de sinal finita nova, demonstrada diretamente das inclusões da fonte, sem receber positividade do pivô.

Base: PR #126, commit `562e8f8302a84f9ffdb2021384ea7a21f2edb14b`, branch `agent/native-radial-flow-audit`. Nova branch: `agent/native-moving-radial-balance`. A #126 foi conferida aberta, draft, sem merge. `main` permanece em `59e53d863f4ef0ad998b0eb19fd3891c9839cc35`. Execução no host `llm`.

O parâmetro h=1/(k+1) é o passo da regularização radial existente. Não é a profundidade vertical Carry nem uma troca de câmera. A escala sqrt(k+1) abaixo já pertence às features radiais originais.

## A — O que já estava demonstrado

- As #124–#125 transportam a mesma fonte pelas cartas Euler/Newton, em qualquer dimensão finita fixada, e identificam o limite de seu balanço e pareamento polarizado com a forma canônica original. Não determinam seu sinal.
- A #126 demonstra uma direção negativa do kernel do gerador R=zQ′/(1+Q²), com Q=−F′/F da característica completada original. Conserva quatro endereços, 16 cruzamentos e toda a cauda analítica. Faltava identificar o readout com o carrier físico e diferenciar a trajetória móvel completa.
- A #41 separa a ortogonalização algébrica, que requer inversibilidade na etapa de Schur, da interpretação positiva. Preservamos essa direção lógica. Não usamos whitening ou positividade de Hankel como premissa.
- `physicalCompletedFiniteSource_original`, `physicalCompletedFiniteSource_fin`, `canonicalCompletedNativeRadialProjectiveChiralState_eq_transform` e `inner_completedNativeChiralCauchyFeature` fornecem a fonte, as duas pernas, a amplitude e a métrica Cauchy existentes.
- `criticalOddSource`, `critical_coefficient_formula` e `critical_source_fixed_jet` já identificam a direção de quatro endereços do segundo pivô ímpar. Seus coeficientes materiais são determinados antes de escolher a como razão de momentos.
- As inclusões `material_theta_integral_input` e `mem_logMomentBox` certificam os momentos originais. Usamos essas inclusões; não seus consumidores de positividade finita.

## B — O que foi demonstrado agora

### B.1 — A mesma curva no carrier físico e na carta Euler/Newton

[OriginalCurve.lean](OriginalCurve.lean) define `curveState N h x` aplicando o **transformador projetivo/chiral existente** às mesmas features Cauchy φᵣ, com escala sqrt(1/h). Em hₖ=1/(k+1), `curve_at_grid` e `curve_eq_original` provam igualdade dos dois vetores completos:

$$U_N(h_k,x)=\mathrm{physicalCompletedFiniteSource}_k(\mathrm{finRadialCoefficients}_N(x)).$$

`curve_euler_newton` identifica esse mesmo estado com a síntese de jets da carta física Euler/Newton da #124. Não se constrói uma família de vetores a partir dos momentos nem se usa uma Gram-alvo.

`curve_legs` conserva as pernas incidente e retornada na forma

$$I=\sum_r c_r\phi_r,\qquad R=\sum_r c_rq_r\phi_r,\qquad
c_r=\sqrt{1/h}\,A(id_rh)x_r,\quad d_r=r+1.$$

Fora da grade, a curva usa a fórmula contínua do transformador existente. A igualdade com o objeto indexado por k foi provada na grade; a derivação não é uma operação diferencial sobre uma sequência em ℕ.

A é `completedNativeNormalizedPositiveChiralAmplitude`, exatamente uma vez; q é o quociente original. A métrica continua sendo a de L²[0,1] das meias densidades originais. Não há projeção ambiente ou alteração de produto interno.

[CurvePairing.lean](CurvePairing.lean) primeiro prova a expansão de todos os cruzamentos desse estado. Com

$$\mathcal F_q(c,d)=\sum_{r,s<N}\overline{c_r}d_s
\frac{1-\overline{q_r}q_s}{r+s+2},$$

`curve_full_pair` demonstra 2B(U(x),U(y))=Fq(c(x),c(y)), em dois argumentos independentes. `curve_norm_balance` e `original_norm_balance` identificam sua parte real com ||I||²−||R||². A escala e a amplitude estão dentro de c; não foram omitidas.

### B.2 — O completamento cancela o denominador do quociente no pareamento completo

`original_amplitude` e `original_returned_amplitude` derivam das definições nativas, onde F e o canal positivo são regulares:

$$A(z)=\frac{Q(z)+i}{\sqrt2},\qquad A(z)q(z)=\frac{Q(z)-i}{\sqrt2}.$$

[CompletionCancellation.lean](CompletionCancellation.lean), teorema `amplitude_defect`, conserva os dois argumentos e demonstra:

$$\boxed{\overline{A(z)}A(w)(1-\overline{q(z)}q(w))
=i(\overline{Q(z)}-Q(w)).}$$

Assim, o denominador associado a q não sobrevive isoladamente no kernel completado. Esta é uma igualdade de cancelamento, não uma declaração de sinal.

Na grade imaginária, Q(idᵣh)=2iρᵣ(h), com ρ o `responseReadout` existente, cuja realidade provém da reflexão nativa já demonstrada. `fullPair_eq_response` e `physical_response_pair` obtêm, depois da síntese vetorial:

$$\boxed{2B(U_N(h,x),U_N(h,y))=
\frac2h\sum_{r,s<N}\overline{x_r}y_s
\frac{\rho_r(h)+\rho_s(h)}{r+s+2}.}$$

Há hipóteses explícitas de regularidade da fonte e h≥0. `curve_regular_eventually` descarrega as condições da fonte, simultaneamente no prefixo finito, perto do centro. Os termos de completion não foram retirados por escolha; sua recomposição é uma igualdade provada.

### B.3 — Derivada da trajetória móvel, com todos os termos

[MovingDerivative.lean](MovingDerivative.lean) prova `fullPair_hasDerivAt` para duas trajetórias independentes c(h),d(h), incluindo a derivada da conjugação sobre o parâmetro real. Na diagonal, a derivada é

$$\boxed{\mathcal F_q(c',c)+\mathcal F_q(c,c')
-\sum_{r,s<N}\overline{c_r}c_s
\frac{\overline{q'_r}q_s+\overline{q_r}q'_s}{r+s+2}.}$$

Os dois primeiros termos são o movimento dos coeficientes; o último é a variação do retorno. O coeficiente c inclui **tanto a escala quanto A e o input material**. Não se pode substituir essa fórmula apenas pelo último termo.

[CurveRegularity.lean](CurveRegularity.lean) demonstra a diferenciabilidade da amplitude e do quociente a partir da característica original, e da escala para h>0. `physical_moving_derivative` aplica a fórmula ao estado físico completo em qualquer dimensão finita. Só se pede diferenciabilidade do input bruto, além da regularidade explícita da fonte.

[CriticalPhysicalBridge.lean](CriticalPhysicalBridge.lean) descarrega também a regularidade do input para a família crítica original. `critical_physical_derivative` não recebe uma condição de sinal nem um gate abstrato de diferenciabilidade do retorno. A derivada é em h; não se aplicou um clock não limitado aos estados sem provar seu domínio.

### B.4 — Teste físico na segunda direção crítica ímpar

Os coeficientes originais são preservados por `critical_raw_at_grid` e `critical_curve_eq_original`:

$$x(h)=\frac{i}{6h^3}w_a(h),\qquad
w_a(h)=(-1,3,-3,1)+6ah^2(-1,1,0,0).$$

O parâmetro a é livre nesta construção. Só depois selecionamos a*=h₂/h₁, a direção crítica algébrica do bloco ímpar 2×2.

[CriticalOddTaylor.lean](CriticalOddTaylor.lean) mantém as 16 interações e o resto analítico original da resposta Q. [CriticalEnergyTransport.lean](CriticalEnergyTransport.lean), `critical_physical_energy`, identifica exatamente esse readout com o balanço das normas da mesma fonte crítica física.

Para Dₖ(a)=||Iₖ(a)||²−||Rₖ(a)||² e hₖ=1/(k+1), obtemos o desenvolvimento com resto analítico completo:

$$D_k(a)=2p(a)+C(a)h_k^2+h_k^3\operatorname{Re}R_a(h_k),$$

$$p(a)=h_3-2ah_2+a^2h_1,\qquad
\boxed{C(a)=-10a^2h_2+168ah_3-60h_4.}$$

O teorema `critical_original_correction_tendsto` formaliza diretamente o limite físico (Dₖ(a*)−2p(a*))/hₖ²→C(a*). O fator 2 é o original, vindo de 2 Re B=||I||²−||R||².

[CriticalOddSign.lean](CriticalOddSign.lean) prova das inclusões integrais existentes:

$$\boxed{-10h_2^3+168h_1h_2h_3-60h_1^2h_4>0.}$$

Também prova h₁>0 pelas mesmas caixas, sem invocar seu antigo consumidor de positividade. Como C(a*)h₁² é exatamente esse polinômio, `critical_correction_positive` conclui C(a*)>0. `critical_original_eventually_above` transporta o sinal ao balanço físico:

$$\boxed{D_k(a_*)>2p(a_*)\quad\text{eventualmente}.}$$

O resultado determina o lado de aproximação do limite, sem pressupor que esse limite seja positivo e sem demonstrar monotonicidade da sequência. Diagnóstico do checkpoint: a*≈0,00387850013647, 2p≈2,07706135×10⁻¹⁰ e C≈2,17515909×10⁻¹⁰. Esses decimais não são premissas Lean.

## C — O que foi refutado ou delimitado

1. Diferenciar só o retorno mantendo implicitamente a amplitude fixa não fornece a derivada da fonte crítica original. A fórmula B.3 mostra os dois termos adicionais e B.2 explicita o cancelamento completado.
2. A correção desta direção ímpar é positiva. Não é legítimo postular que todas as correções tenham sinal negativo ou que uma orientação observada numa direção seja universal.
3. A obstrução da #126 permanece válida para seu kernel R e sua testemunha racional 7/1000. A direção crítica desta etapa usa a*=h₂/h₁, um parâmetro diferente. Não afirmamos que a mesma testemunha negativa tenha sido transformada numa direção positiva por alteração de fonte ou métrica.
4. Dₖ>2p não demonstra p>0. O sinal da aproximação e o sinal do limite são obrigações diferentes. A positividade finita desse pivô já existente não entra nas provas novas.

O script [mechanism_probe.py](mechanism_probe.py) verifica 625 identidades gaussianas racionais em dois argumentos, 320 contribuições exatas dos filtros e quatro diagnósticos completos dos dois canais. Os diagnósticos usam os 64 `canonical_h` históricos a 120 dígitos, sem recalcular momentos. Não possuem cota analítica de truncamento; as provas Lean usam a fonte e o resto completos.

## D — O que permanece aberto

- Não foi provada positividade de Hankel em toda ordem. As identidades de curva e derivada valem em qualquer dimensão finita; a desigualdade C>0 foi certificada somente nesta direção ímpar.
- Não se afirma convergência separada das duas pernas; o limite investigado é o balanço completo.
- Não há uniformidade na dimensão ou passagem a um operador infinito. A regularidade é local no centro, para cada prefixo finito.
- Os resultados não identificam isoladamente cada parcela da derivada como positiva. A amplitude, o input e o retorno devem continuar juntos.
- As realizações H6/K6 e de doze fontes permanecem como resultados finitos anteriores, sem serem premissas deste avanço. Não há novas alturas ou zeros fornecidos como entradas ou certificados como saídas.
- Continua faltando uma desigualdade independente da fonte que determine o sinal do residual canônico completo em toda ordem. Derivar exatamente a trajetória não descarrega essa obrigação de sinal.

## E — Próximo passo mínimo e reprodução

O transporte do kernel para o carrier físico e a regra da derivada móvel deixaram de ser gates abertos. O próximo passo concreto é simplificar a **soma das três variações** usando B.2, em coordenadas materiais originais, e investigar sua parte assinada acumulada.

O alvo explícito, ainda não formalizado como fórmula fechada nesta entrega, é a derivada da expressão de B.2: os termos de x′ somados ao kernel h(ρ′ᵣ+ρ′ₛ)−(ρᵣ+ρₛ), com todos os cruzamentos e o fator 2/h². Isso permite testar uma estimativa relativa do conjunto sem voltar ao gerador R isolado. A estimativa de sinal precisa ser derivada da fonte; não pode receber p>0, PosDef ou contração equivalente como nova hipótese.

O teste seguinte deve preservar a mesma síntese em seis endereços e confrontar a fórmula geral com a direção crítica algébrica correspondente. Esse teste pode refutar uma orientação universal, mas não substituir uma lei all-order. Não é necessário recalcular milhares de momentos ou repetir a certificação dos pivôs já conhecidos.

Reprodução no host `llm`, na pasta desta pesquisa:

```bash
python3 restore_verified_cache.py
python3 validate.py --reuse-upstream
```

O cache opcional da #126 contém 170 objetos, verificados contra fontes, hashes, toolchain, manifesto, operador e pins. SHA256: `02638bfdc8b3fe1673cfd7a5e32ec027d7836ee8333b75f2ba2e4d4a64ac8cbf`. Deve estar em `.cache/input-cache.tar.gz`. Sem ele, `python3 validate.py` recompila os ancestrais a partir das fontes históricas exatas. A nova pesquisa compila seus módulos e a auditoria novamente, sem campanha nova de quadratura.

Checkpoint diagnóstico: `momentos/native_jet_exploration/auditoria_corrected_vs_canonical/stage_A/moments.csv`, coluna `canonical_h`, SHA256 `05734f8898aae995d77360c79e60521855181fede3f7f2a46c6b1bc1bc8e1833`. O arquivo não participa das provas Lean.

### Validação concluída

**22 checks passaram**, todos com exit 0. São **48 teoremas e 22 definições públicas**, em nove módulos matemáticos novos, além do módulo Audit gerado. As compilações individuais usam warnings como erros. Passaram os alvos nativos selecionados, `lake build --wfail` e as auditorias Foundation/Geometry/Analysis.

Foram reutilizados e verificados os 170 objetos da #126, incluindo seus certificados integrais antigos; nenhum foi anunciado como recompilado nesta execução. As 625 identidades gaussianas racionais, 320 contribuições exatas dos filtros e quatro diagnósticos dos canais completos passaram.

As 70 raízes públicas possuem `#print axioms` e auditoria transitiva de tipos e corpos, incluindo opacos com `value? (allowOpaque := true)`. O grupo algébrico tem 19 raízes e 42683 dependências; o grupo da fonte, 44 e 62198; o grupo de certificação, 7 e 58494. Os certificados finitos de positividade canônica enumerados e as equivalências de positividade indicadas estão proibidos na auditoria. A certificação exige a presença efetiva das inclusões integrais, da identificação da energia física original e do resto analítico completo. Só são aceitos os axiomas fundacionais `propext`, `Classical.choice`, `Quot.sound`.

Não há `sorry`, `admit`, `native_decide` ou novos axiomas. Fontes, pesos, métricas, amplitudes, dressing, completion, pins e trabalhos antigos foram preservados. As evidências estão em `evidence/validation.json`, `evidence/kernel-audit-summary.json`, `evidence/upstream.json` e `evidence/preservation.json`; `SHA256SUMS` registra os arquivos da entrega. Validação observada no host `llm`, sem reivindicação de CI externo.

A publicação usa PR draft empilhada sobre a #126, sem merge automático. Fontes e cache verificados são arquivados localmente antes da remoção somente do worktree próprio; a branch e todos os trabalhos anteriores são preservados.

Fim do relatório — mesma fonte física, derivada móvel completa e orientação ímpar certificadas; lei canônica de sinal em toda ordem permanece aberta.
