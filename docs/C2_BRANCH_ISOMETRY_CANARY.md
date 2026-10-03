# Canário: realização Hilbert real do operador de ramo C2

## STATUS

**PASS — the critical historical C2 branch operator has a canonical real Hilbert realization and is an exact isometry before any Parseval whitening.**

Trabalho isolado na branch `canary-c2-branch-isometry`, sobre
`93c96c0952bceacaf3fd2b9b0bb5eb03cce7fc0f`. Sem commit, merge ou push.
Os canários anteriores e R2 foram preservados. A família em sigma continua
sendo uma comparação radial downstream; não fornece uma nova origem da
amplitude crítica.

## HISTORICAL OPERATOR

Especificação lida literalmente em
`formalizacao_C2/operadores/cp_branch_operator.py`, SHA
`dc35555879e3c0f188508c729c4a0ea31be246fb`:

| Item | Especificação histórica |
|---|---|
| Domínio | Escalar complexo `z` |
| Contradomínio pretendido | `ell²(A_p × {k0,k0+1,...})` |
| Coeficiente | `cmath.exp(-k * complex(sigma,t) * log(p))` |
| C2 | `legs = (-1,1)`, `k0 = 2` por padrão |
| Norma quadrática | `branch_count * q**k0 / (1-q)`, `q=p**(-2*sigma)` |
| Implementação Python | Aplicação finita até `K`; norma infinita pela forma fechada |

O Python permite sobrescrever `k_start`. Esta rodada realiza o C2 canônico
com `k0=2`, não essas variantes. O Python não foi executado nem utilizado
como prova. O elemento Hilbert infinito é construído no Lean.

O início em profundidade dois e as duas direções possuem referências locais
pré-existentes em `C2BranchOrbitCanary`: `c2BranchDepth_ge_two_iff_center_four_dvd`
(core ímpar) e `c2BranchDirections_card`. A mudança `j ↦ j+2` permanece explícita.

## REAL CARRIER

~~~lean
RealPlaneHilbert := EuclideanSpace ℝ (Fin 2)
C2BranchDirection := Fin 2
C2BranchCarrier := ℓ²(C2BranchDirection × ℕ, RealPlaneHilbert)
~~~

`c2BranchDirectionSign` associa 0 a −1 e 1 a +1.
O primeiro `Fin 2` identifica direções; o `Fin 2` interno identifica
quadraturas. Não há identificação entre esses índices ou entre profundidade
e coordenada material.

`RealPlaneState = ℝ × ℝ` conserva sua energia polinomial e suas instâncias.
A norma usual desse produto é a norma máxima, portanto não foi usada como
norma Hilbert. `realPlaneHilbertEquiv` é uma equivalência **linear algébrica**,
e o theorem `realPlaneHilbert_energy_eq_norm_sq` prova:

$$
E(e^{-1}v)=\|v\|^2.
$$

Nenhuma equivalência isométrica com a norma máxima foi afirmada.

## POINTWISE CROSSWALK

A definição `realBranchOperator sigma t hsigma v` usa, em `(a,j)`:

$$
e\left(F_{\sigma,t}^{[j+2]}(e^{-1}v)\right).
$$

`realBranchOperator_apply` prova essa leitura; a forma fechada é provada por
`c2DeformedFiberStep_iterate_eq_radial_rotation` e
`realBranchOperator_apply_closed_form`:

$$
e^{-1}(W_{\sigma,t}v)_{a,j}
=2^{-(j+2)\sigma}
 R_{-(j+2)t\log2}(e^{-1}v).
$$

Os dois ramos recebem a mesma órbita, como na especificação histórica.
Eles não são identificados com os vetores das pernas físicas
`2^k m ± 1`: os log-defects dessas pernas continuam preservados no canário
anterior. O parâmetro `t` permanece na definição de W.

O crosswalk complexo opcional não foi implementado; toda a construção e
todas as provas de norma usam ℝ e ℝ².

## L2 MEMBERSHIP

Para `0 < sigma`:

1. `realBranchCoordinates_norm_sq` reutiliza a energia iterada já provada;
2. `realBranchCoordinates_square_summable` reutiliza
   `c2BranchUnitOrbitEnergy_summable`, multiplica pela energia do vetor e
   soma sobre as duas direções finitas;
3. `realBranchCoordinates_mem_l2` fornece a prova `Memℓp ... 2`;
4. `realBranchOperator` empacota o elemento efetivo de ℓ².

Não há argumento numérico ou truncamento na prova de somabilidade.

## LINEARITY

`c2DeformedFiberStepLinear` empacota a linearidade de rotação e escala
coordenadas. Dois lemas privados levantam adição e multiplicação escalar
pela iteração. `realBranchOperatorLinear` é o mapa ℝ-linear completo.

## NORM IDENTITY

`realBranchOperator_norm_sq` prova, para `0 < sigma`:

$$
\boxed{\|W_{\sigma,t}v\|^2=M(\sigma,t)E(e^{-1}v).}
$$

A prova usa a fórmula de norma de ℓ², a soma sobre `Fin 2`, a identidade
de energia iterada e **o mesmo** `c2BranchOrbitMass` do canário anterior.
`realBranchOperator_norm_sq_of_realPlaneState` dá a forma para o estado
original `u`: `‖W(e u)‖² = M E(u)`.

`realBranchOperator_norm_sq_eq_legacyBranchNormSq` fornece o crosswalk
literal com `legacyC2BranchNormSq`. Por `realBranchOperator_norm_independent_time`,
a norma independe de `t`, embora W dependa dele.

## CRITICAL ISOMETRY

`realCriticalBranchOperator_norm` especializa a identidade geral usando
somente `c2BranchOrbitMass_half` e a igualdade energia/norma euclidiana:

$$
\boxed{\|W_{1/2,t}v\|=\|v\|.}
$$

`realCriticalBranchIsometry t` empacota:

~~~lean
RealPlaneHilbert →ₗᵢ[ℝ] C2BranchCarrier
~~~

`realCriticalBranchIsometry_apply_centerStep` identifica suas coordenadas
com a iteração do `c2CenterFiberStep t` preexistente, por composição com
`c2DeformedFiberStep_half_eq_c2CenterFiberStep`.

## ADJOINT

**PROVED**: `realCriticalBranch_adjoint_comp_self`:

$$
\boxed{W_t^*\circ W_t=I.}
$$

É aplicação direta de `LinearIsometry.adjoint_comp_self` da Mathlib aos
dois Hilbert reais completos. Não há cálculo coordenado de adjunto nem
normalização adicional. A identidade não afirma sobrejetividade.

## PARSEVAL RELATION AUDIT

**NO_RELATION_FOUND**, nos objetos concretos consultados. Isso registra
ausência de uma ponte encontrada nesta auditoria; não prova inexistência
de relações em todo o corpus histórico.

| Pergunta | Resultado |
|---|---|
| W crítico satisfaz `W*W=I` antes de whitening? | SIM, theorem local acima |
| T consultado contém W explicitamente como bloco? | NÃO encontrado |
| Há theorem de inclusão/intertwining encontrado? | NÃO |
| A identificação com o T posterior está fechada? | NÃO; interface de bloco permanece aberta |

Evidência de tipos/definições, somente leitura:

- `carry-self-adjoint-operator`, SHA `cb33c845a7ee0ca1c6bf195d34d7f3ac1628edfa`,
  `BR2GreenFrameDslopeLimitBridge.lean:36–61`: análise all-bases a partir do
  carrier vertical e composição com `canonicalParseval`.
- Sua dependência `GreenFrame`, SHA
  `cd2d838bee67ad23f869a02f8ed9f0a0feb926fa`:
  `ConcreteSplitOperators.lean:23–65` define
  `T=((seed,residual,G₁),G≥2)` a partir de `State=ℓ²(PNat,ℂ)`.
- `GreenDepthSectorEnergy.lean:49–89` indexa o bulk por eventos com
  `HasGrandparent`; `GreenStencilComplex.lean:163–165` lê
  `greenAmplitude * verticalGreenStencil`. Essas coordenadas não são
  definidas como `F^[j+2]v` de um vetor ℝ².
- `CanonicalParseval.lean:21–86` define `T ∘ (T* T)^(-1/2)` e sua
  isometria. Essa construção foi **apenas auditada**, não importada ou
  usada para provar nenhum resultado novo.

Buscas registradas incluem os nomes de ramo/legado em `CarrySelfAdjointOperator`
e `GreenFrame`: as ocorrências de barreira escalar não forneceram uma
inclusão do operador W no T concreto. No projeto novo, R2 conserva
`S ∘ T=I`; nenhum desses mapas foi alterado ou usado na prova de W.

## AXIOMS / VALIDATION

Todos os 25 nomes públicos novos possuem `#assert_analysis_axioms` e
`#print axioms` em `Analysis/Audit.lean`. Cada capstone de norma, isometria
e adjunto tem exatamente:

~~~text
[propext, Classical.choice, Quot.sound]
~~~

O alias `C2BranchDirection` não possui axiomas; o sinal usa `propext`;
sua verificação dos dois valores usa `propext, Quot.sound`.
O arquivo `AXIOMS.json` registra o resultado por nome.

Validação: builds isolado/Analysis/Audit, scripts audit-foundation,
audit-geometry, audit-analysis, `git diff --check`, busca de placeholders
e comparação dos arquivos anteriores por SHA256. Exemplos formais
incluem ambas as etiquetas, energia da primeira coordenada `E/4`,
linearidade, seed unitário em qualquer tempo e retorno pelo adjunto.
Os logs e resultados estruturados estão na pasta de artefatos desta rodada.

## FILES

Novos:

- `GeometryOfNumbers/Analysis/C2BranchIsometryCanary.lean`;
- `docs/C2_BRANCH_ISOMETRY_CANARY.md`.

Modificados apenas por adições desta rodada:

- `GeometryOfNumbers/Analysis.lean`: import do novo módulo;
- `GeometryOfNumbers/Analysis/Audit.lean`: guards, prints e exemplos;
- `docs/SOURCE_PROVENANCE.md`: proveniência append-only.

R2, Foundation, Geometry e os canários anteriores não foram modificados.
As alterações paralelas da main foram preservadas. Não há commit novo.

## SEMANTIC CONCLUSION

**SIM.** Para o operador C2 puro especificado historicamente, a saturação
`BranchMass=1` especializa a identidade de norma do próprio operador e
produz literalmente uma isometria real, antes de qualquer whitening.

Massa unitária não implica genericamente isometria. Aqui ela funciona
porque a identidade `‖Wv‖² = M E(v)` foi provada para todo vetor no domínio.
A invariância angular elimina `t` da norma, preservando sua presença no
operador. Nenhuma conclusão sobre o operador auto-adjunto é feita.
