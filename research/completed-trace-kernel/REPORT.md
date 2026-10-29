# Traços completados, pareamento Mellin e defeito entre grades radiais

**Resultado: PARTIAL.** A comparação pedida ao final da PR #78 foi
formalizada: os traços das seis componentes físicas, o pareamento Cauchy
completo e o bordo de Euler foram transportados para o pareamento Mellin
original. As diferenças entre essas operações foram calculadas exatamente.
A Gram positiva canônica all-order permanece aberta.

Branch: `agent/completed-trace-kernel`. Base imutável:
`4f98f0343b596f3c133d42dfb1ea3055fa069664`, head consultado da PR #78.
`origin/main` foi atualizado por fetch e permaneceu em
`59e53d863f4ef0ad998b0eb19fd3891c9839cc35`.
O operador consultado é `bfeb10fd2425400fa38139903d12bf0599f02e53`.
Não foram modificados fontes históricas, pins, métricas, fases ou pesos.
As PRs anteriores não foram mescladas; a #41 permanece independente.

## A — O que já estava demonstrado

Da PR #78 foram reutilizados `EndpointDomain`, `endpointTrace`,
`endpoint_green`, `radial_finite_material` e os teoremas de pertença das
pernas e dos canais completados ao núcleo físico. O traço é definido no
núcleo algébrico com coeficientes únicos; não é avaliação de um
representante arbitrário de `Lp` e não se supõe contínuo no fecho inteiro.

Da PR #76 foi reutilizado, por import e recompilação efetivos,
`CarryCompletedPairing.completed_pairing_eq_original`: para parâmetros
admissíveis, `completedIntegralPairing A B z w` é o Wronskiano da
característica e do companion originais, com cutoffs independentes.
Cabeça, caudas e completion continuam dentro dessa definição.

No operador foram reutilizados:

- `physicalSourceValue`, `physicalSourceCompanion`,
  `physicalNativeCompanion`, `physicalCompletionCompanion`,
  `physicalOriginalIncident` e `physicalOriginalReturned`.
- `ChiralReturn.sourceCompanion_eq_native_add_completion`.
- `canonicalCompletedNativePolarizedDslopeKernel_eq_positive_mul_pick`:
  fatoração assinada do kernel canônico, sob suas hipóteses de domínio
  e denominadores, sem conclusão incondicional de positividade.
- `ChiralReturn.hasDerivAt_storage` e
  `two_point_storage_nonnegative_but_endpoint_flux_negative`: o saldo de
  bordo negativo com coeficientes opostos já era conhecido. Não é
  anunciado como nova descoberta desta investigação.
- `completedNativeHermiteBiehlerChiralPickKernel_central_diagonal_tendsto`
  e o sinal independente do primeiro momento, apenas no canário final.

A PR #41 separa ortogonalização algébrica, inversibilidade e sinal do
residual. Seu head consultado continua
`ee56930a2c30456cfbd214a29bb31b12d3977204`, aberto. Não se fingiu um import
dessa branch nem se usou positividade all-order como premissa.

Foram recompilados **30 módulos ancestrais reais**, em ordem de
dependência. Os hashes das fontes foram confrontados com o commit-base;
o registro está em `evidence/source-provenance.json`.

## B — O que foi demonstrado agora

### 1. Traços dos seis canais físicos originais

`SourceReadouts.lean` restringe o contradomínio dos seis vetores existentes
ao núcleo a que já pertencem. Não constrói estados a partir dos momentos.

Escreva \(\kappa=k+1\) e
\(z_i=\mathrm{i}(i+1)/(k+1)\). Defina o peso original

\[
a_i=\frac{c_i r^{i+1}}{H^+(z_i)}.
\]

Para toda ordem material de jet \(m\), foram provadas as fórmulas

\[
\begin{aligned}
\tau_m(V)&=\sqrt\kappa\sum_i i^{\underline m}a_i F(z_i),\\
\tau_m(C)&=\sqrt\kappa\sum_i i^{\underline m}a_i[-F'(z_i)],\\
\tau_m(C_{\rm native})&=\sqrt\kappa\sum_i i^{\underline m}a_i
 A(z_i)\Psi_{\rm native}(z_i),\\
\tau_m(C_{\rm completion})&=\sqrt\kappa\sum_i i^{\underline m}a_i
 A_{\rm companion}(z_i)N(z_i).
\end{aligned}
\]

São `value_core_trace`, `companion_core_trace`, `native_core_trace` e
`completion_core_trace`. `incident_core_trace` e `returned_core_trace`
mantêm a mesma expressão nos coeficientes de incidência e retorno, com
o quociente completado original \(q(z_i)\) no retorno.

`companion_core_split` aplica a decomposição no nível vetorial, antes
dos traços; `companion_trace_split` a transporta. O termo de derivada do
completion, incluindo sua proveniência Gamma, não foi removido.

O índice radial \(k\), o endereço material \(i\), a ordem do jet \(m\)
e a profundidade vertical Carry são dados diferentes. Nenhum foi
identificado com outro por conveniência.

### 2. Duas entradas independentes e o residual bordo–interior

Seja

\[
W(z,w)=(-F'(z))\overline{F(w)}-F(z)\overline{-F'(w)}.
\]

`completed_trace_pairing_mellin` prova, com suportes, entradas, raios,
índices radiais e cutoffs independentes,

\[
T_{k\ell}=\sqrt\kappa\sqrt\lambda
 \sum_{i,j}a_i\overline{b_j}\,
 \operatorname{completedIntegralPairing}_{A,B}(z_i,w_j).
\]

Aqui \(T\) é o wedge dos traços das fontes completas. Não se afirma que
esse wedge seja uma norma positiva. `completed_euler_pairing_mellin`
identifica a mesma expressão com os **quatro pareamentos de Euler** na
métrica original, por `euler_wedge_trace`.

O pareamento físico original é outra operação:

\[
\mathcal B_{k\ell}=\langle V_k,C_\ell\rangle-
 \langle C_k,V_\ell\rangle.
\]

`physical_mixed_pairing_mellin` prova

\[
\boxed{
\mathcal B_{k\ell}=\sum_{i,j}\overline{a_i}b_j G_{ki,\ell j}
 \operatorname{completedIntegralPairing}_{B,A}(w_j,z_i),
\qquad
G_{ki,\ell j}=\frac{\sqrt\kappa\sqrt\lambda}{i+j+2}.
}
\]

A troca de argumentos e de cutoffs no lado direito preserva a orientação
conjugada do primeiro argumento do produto interno. Ela não é omitida.

Finalmente, `boundary_minus_bulk_mellin` calcula a diferença literal:

\[
\boxed{
T_{\ell k}-\mathcal B_{k\ell}
=\sum_{i,j}\overline{a_i}b_j
 (\sqrt\kappa\sqrt\lambda-G_{ki,\ell j})
 \operatorname{completedIntegralPairing}_{B,A}(w_j,z_i).
}
\]

Portanto, substituir o pareamento Cauchy pelo bordo de Euler apaga um
fator geométrico em cada cruzamento. O fator não pode ser descartado
porque o bordo possui alguma expressão positiva isolada.
`completed_trace_split` conserva explicitamente os dois companions
independentes, nativo e completion, em ambos os argumentos.

### 3. Fator exato entre grades radiais e o kernel canônico

Em `CrossRadialGeometry.lean`, o defeito quiral original é

\[
D_{k\ell}(i,j)=G_{ki,\ell j}
 [1-\overline{q(z_i)}q(w_j)].
\]

`cross_defect_is_original_pairing` identifica essa expressão com a
diferença dos dois produtos internos físicos originais. Com \(P\) o
kernel Pick já existente, provou-se

\[
\boxed{D_{k\ell}(i,j)=\rho_{k\ell}(i,j)P(z_i,w_j)},
\]

onde o fator geométrico **não ajustado** é

\[
\boxed{
\rho_{k\ell}(i,j)=
\frac{\sqrt\kappa\sqrt\lambda}{i+j+2}
\left(\frac{i+1}{\kappa}+\frac{j+1}{\lambda}\right).
}
\]

São `cross_defect_eq_factor_pick` e `mixed_radial_separation`.
`cross_factor_same_radial` recupera \(\rho_{kk}=1\), coerente com os
resultados históricos de uma única grade. `native_kernel_cross_factor`
transporta a fórmula para o kernel **canônico concreto**:

\[
\boxed{P_+(z_i,w_j)D_{k\ell}(i,j)
=\rho_{k\ell}(i,j)K_{\rm can}(z_i,w_j).}
\]

\(P_+\) é o kernel positivo normalizado já definido na fonte; suas
normalizações não foram trocadas. As hipóteses de strip e não anulação
dos denominadores permanecem explícitas.

## C — O que foi refutado ou distinguido

### Mesmo parâmetro espectral não é o mesmo estado material

`doubled_radial_same_point` prova

\[
z_{k,0}=z_{2k+1,1},
\]

mas `same_parameter_state_difference_norm_sq` prova

\[
\boxed{
\|\phi_{k,0}-\phi_{2k+1,1}\|^2
=(k+1)\left(1-\frac{2\sqrt2}{3}\right)>0.
}
\]

`same_parameter_states_ne` formaliza a desigualdade dos estados, sem
momento ou hipótese de sinal canônico. O retorno continua com seu
quociente original, por `same_parameter_return_difference`.

Logo, identificar esses estados porque fornecem o mesmo parâmetro
espectral apagaria informação material independente. Este resultado
não chama essa diferença de redundância física.

Para esse mesmo teste, `cross_factor_same_point` fornece
\(\rho=2\sqrt2/3<1\). `cross_defect_same_point_residual` calcula

\[
D_{k,2k+1}(0,1)-P(z,z)
=\left(\frac{2\sqrt2}{3}-1\right)P(z,z).
\]

O canário tardio `cross_radial_residual_re_negative_eventually` demonstra
que a parte real desse residual é estritamente negativa eventualmente,
usando somente o sinal independente do primeiro momento e o limite
diagonal nativo já provados. Assim, a igualdade sem fator realmente
falha na fonte concreta; não é apenas uma diferença formal de fórmulas.

### O traço novo reproduz o fluxo assinado histórico

`endpoint_balance_is_native_flux` prova que a diferença das energias dos
traços das duas pernas, no bordo 1, é exatamente a derivada do storage
nativo nesse bordo. `endpoint_balance_opposite_negative` reutiliza o
contraexemplo histórico de coeficientes \((1,-1)\).

Isso refuta uma interpretação universalmente não negativa desse bordo,
não a positividade do storage integrado ou uma eventual Gram canônica
completa. Não se refez o resultado histórico como se fosse novo.

## D — O que permanece aberto; contribuição das notas de Momentos

Não há nesta PR uma família física positiva satisfazendo
\(h_{i+j}=\langle V_i,V_j\rangle\) em toda ordem. Os jets canônicos já
identificados na PR #76 não se tornam Grams ao substituir um desses
pareamentos pelo outro. As fórmulas acima calculam precisamente a
diferença que essa substituição deixaria.

O fator \(\rho\) é um cruzamento **radial/material**. Não é a troca de
câmera, a escala quadrática Carry ou o acoplamento \(b_n^2\) da Jacobi.
Sua positividade por entrada também não fornece, por si só, uma
transformação que preserve positividade de matrizes.

### Publicação de Momentos conferida durante a investigação

Foi confirmado via API autenticada que o `main` remoto de
`thiagomassensini/momentos` apontava para
`0d0dd0975a1558ced731e9246c14420c0e0720f4`, com os três arquivos informados.
O checkout local desse repositório tinha uma edição preexistente em
`AUDITORIA_CORRECTED_MOMENTS_VS_CANONICAL_RECURRENCE.md`; não foi atualizado
nem modificado. Os dados foram lidos diretamente do
[commit imutável](https://github.com/thiagomassensini/momentos/commit/0d0dd0975a1558ced731e9246c14420c0e0720f4).

O programa publicado foi reproduzido com Python 3.12 e mpmath 1.3.0,
usando 100 DPS, com erro relativo máximo **1.6711435e-99**.

`verify_momentos.py` fez também uma verificação independente em
`Fraction`, tratando os decimais publicados como racionais exatos.
Os polinômios foram obtidos por solução direta das equações Hankel,
sem usar a recorrência de três termos como método de construção.
Passaram exatamente:

- 72 igualdades de reconstrução nos prefixos de ordens 1 a 8;
- 7 identidades do primeiro momento par omitido;
- 7 identidades do primeiro momento ímpar omitido;
- 8 identidades da recorrência de três termos;
- positividade dos 8 pivôs da Hankel de referência desses decimais.

Foi usada a matriz de multiplicação na base **mônica**, com subdiagonal
1 e superdiagonal \(b_n^2\), evitando raízes quadradas na checagem exata.
Isso não é outro operador físico proposto: é somente o verificador
algébrico dos dados finitos publicados.

As notas ajudam a conectar o residual da linha #41 à interpretação de
Jacobi:

\[
h_{2n}-h_0(J_n^{2n})_{00}=q_n,
\qquad b_n^2=q_n/q_{n-1}.
\]

Não determinam o sinal de \(q_n\) da fonte completada em toda ordem.
Na versão sem positividade, convém chamar a razão de \(\beta_n\): ela
pode ser negativa; só quando positiva admite o acoplamento real
\(b_n=\sqrt{\beta_n}\). A identidade universal não remove a obrigação
de sinal nem o defeito físico calculado nesta investigação.

O módulo atual `JacobiOrderPolynomial.lean` de fato define uma recorrência
abstrata. A identificação com o polinômio característico da Jacobi
canônica concreta não foi demonstrada nesta PR. Os testes racionais
não são provas Lean dessa identificação universal, nem certificados
dos integrais canônicos originais.

## E — Próximo passo mínimo, validação e reprodução

A próxima obrigação concreta é calcular o **limite polarizado dos jets
físicos com dois índices radiais independentes**, começando pelo jet
zero e por uma razão fixa entre os índices. O fator \(\rho_{k\ell}\)
agora está explícito; não se pode inferir esse limite a partir da
igualdade de uma única grade ou da convergência das diagonais.

Se a identificação do kernel único exigir um transporte entre os estados
radiais, ele deve vir das relações físicas originais e preservar os
cruzamentos ou exibir seu complemento. Não se permite remover \(\rho\)
por uma nova métrica, nem identificar estados independentes porque
seus readouts coincidem.

Na linha paralela da #41, as notas de Momentos indicam uma formalização
legítima da reconstrução universal e do primeiro retorno, sob condições
explícitas de admissibilidade. Ela deve permanecer separada da prova
do sinal físico. Nenhum dos dois caminhos autoriza extrapolar os
certificados finitos para positividade all-order.

Validação desta etapa:

- **40 teoremas novos e 15 definições**, em quatro módulos Lean.
- 55 raízes públicas auditadas por `#print axioms` e inspeção transitiva
  dos tipos/corpos: 5.622 dependências no conjunto completo.
- O grupo de fonte/comparação tem 52 raízes e 5.589 dependências, sem
  construção a partir dos momentos ou certificados finitos de sinal.
- Os três canários de sinal são auditados separadamente; somente eles
  usam sinais nativos já estabelecidos. Não demonstram sinal all-order.
- **14 comandos com saída zero**, incluindo módulos focados, builds
  `--wfail`, auditorias Foundation/Geometry/Analysis e preservação da base.
- 30 módulos ancestrais recompilados; somente `propext`,
  `Classical.choice` e `Quot.sound` na camada analítica nova. Não se
  reivindica footprint vazio nessa camada.

Reprodução no host `llm`, a partir deste diretório:

```bash
python3 build_upstream.py > upstream-build.log 2>&1
python3 validate.py
MOMENTOS_PYTHON=/home/thlinux/miniforge3/bin/python python3 verify_momentos.py
```

O último comando precisa do acesso GitHub já configurado e do mpmath no
Python indicado. Não instala dependências e não edita o checkout de
Momentos. Hashes, comandos, logs, resultados racionais e delimitação de
escopo estão em `evidence/`.

**FIM DO RELATÓRIO — PARTIAL; positividade canônica all-order aberta.**
