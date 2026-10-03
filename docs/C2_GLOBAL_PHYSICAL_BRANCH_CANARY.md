# Global physical C2 branch canary

## STATUS

**PASS — the fixed-core physical C2 branch isometries glue orthogonally into a global real isometry from odd-core states to the odd material sector, with unique material provenance.**

Resultado verificado pelo kernel Lean 4.32.0 no servidor `llm`. Trabalho em
`/home/thlinux/geometry-of-numbers-phase-canary`, branch
`canary-c2-global-odd-source`, HEAD inicial/final
`93c96c0952bceacaf3fd2b9b0bb5eb03cce7fc0f`. Sem commit, merge ou push.

O resultado fecha somente o setor C2 ímpar `n ≥ 3`. A bijeção é dos **índices**;
a source global é uma isometria linear, sem afirmação de sobrejetividade sobre
todos os vetores de `OddMaterialState`.

## CORE INDEX

```lean
PositiveOddCore := {m : ℕ // 0 < m ∧ Odd m}
```

Subtipo natural, sem enumeração escolhida. Cada core guarda positividade e
oddness explicitamente.

## GLOBAL ADDRESS

```lean
GlobalC2BranchAddress := PositiveOddCore × C2BranchAddress
C2BranchAddress := Fin 2 × ℕ
OddMaterialIndex := {n : PNat // Odd (n : ℕ) ∧ 3 ≤ (n : ℕ)}
```

Para `i=(m,(a,j))`, `k=j+2`; `a=0` significa `−1`, `a=1` significa `+1`.
`globalC2MaterialAddress i` reutiliza a avaliação local:

$$n=2^{j+2}m+a_{\rm signed}.$$

- Injetividade global: `globalC2MaterialAddress_injective`.
- Oddness e domínio: `globalC2MaterialAddress_odd`, com o limite local `≥3`.
- Existência **e** unicidade para cada material: `globalC2MaterialAddress_unique`.
- Equivalência: `globalC2BranchAddressEquivOddMaterial`.

### Inversa explícita

Para um material ímpar `n≥3`, selecionar:

$$c(n)=\begin{cases}n+1&n\bmod4=3,\\n-1&n\bmod4=1.\end{cases}$$

Este centro é positivo e divisível por quatro. Então:

$$k=c(n).\mathrm{factorization}(2),\qquad
m=\frac{c(n)}{2^k},\qquad j=k-2.$$

O sinal é `−1` no primeiro caso e `+1` no segundo. `m` é positivo ímpar;
`k≥2`; `2^k m=c(n)`. A função `oddMaterialC2Address` contém essa construção,
sem `Classical.choose` para selecionar um endereço.

O uso da fatoração é certificado **downstream** pela relação já existente:
`oddMaterialNeighbor_depth_crosswalk` aplica
`primeResidualDepth_iff_le_factorization`. Não se redefiniu a profundidade da
torre por valuation ou máximo. O theorem `globalC2_provenance_roundtrip`
certifica todos os thresholds efetivos das pernas:

$$\mathrm{C2LegHasCarryDepthAtLeast}(n,r)\iff r\le k.$$

Injetividade usa esses thresholds para recuperar `k`, o resíduo módulo quatro
para recuperar o sinal e o quociente pelo centro para recuperar o core.

## GLOBAL BRANCH CARRIER

```lean
GlobalC2BranchCarrier := ℓ²(GlobalC2BranchAddress, RealPlaneHilbert)
CoreState := ℓ²(PositiveOddCore, RealPlaneHilbert)
RealPlaneHilbert := EuclideanSpace ℝ (Fin 2)
```

Foi usada a apresentação achatada core × sinal × depth. Não foi necessário
introduzir uma segunda equivalência entre carriers aninhados e achatados.
A energia original em `RealPlaneState` continua sendo `x²+y²`; seu crosswalk
com a norma euclidiana é o já existente `realPlaneHilbert_energy_eq_norm_sq`.

## ODD MATERIAL STATE

```lean
OddMaterialState := ℓ²(OddMaterialIndex, RealPlaneHilbert)
```

As duas quadraturas reais permanecem em cada coordenada material. O seed `n=1`
e todo o setor par ficam fora deste índice.

## INCIDENCE EQUIVALENCE

```lean
globalBranchIncidenceIsometry :
  GlobalC2BranchCarrier ≃ₗᵢ[ℝ] OddMaterialState
```

A avaliação é `X (oddMaterialC2Address n)`; a inversa avalia no material do
endereço. Os roundtrips vêm da equivalência explícita dos índices. A norma é
preservada por reindexação da soma quadrática, não por física:

- `globalBranchIncidenceIsometry_apply_address`;
- `globalBranchIncidenceIsometry_norm`.

## GLOBAL SOURCE

A fibra `criticalPhysicalCoreFiber m t` é a composição **preexistente** da
rotação exata das pernas com o ramo crítico, antes da incidência material.
`criticalPhysicalCoreFiber_eq_local_physical` identifica sua coordenada com a
isometria física local já fechada.

`globalCriticalPhysicalBranch t` aplica essas fibras pointwise aos cores;
`globalCriticalPhysicalBranchIsometry t` compõe com a incidência bijetiva.

Se `oddMaterialC2Address n=(m,(a,j))` e `k=j+2`, o theorem
`globalCriticalPhysicalBranchIsometry_pointwise` prova literalmente:

$$
(\mathrm{GlobalW}_tV)(n)
=2^{-k/2}R_{-t\log n}V(m).
$$

A igualdade Lean é expressa pelo `realPlaneHilbertEquiv.symm`, preservando as
duas coordenadas reais e a energia original. A correção logarítmica das pernas
está retida pela composição local, não aproximada por zero.

**Amplitude:** `2^(-k/2)`, com `k` recuperado do endereço. **Fase:** `−t log n`,
com `n` material. Não há substituição da amplitude por `n^(-1/2)`.

`globalCriticalPhysicalBranch_single_core` demonstra, para **todo** `n` no
setor ímpar, incluindo pontos fora do suporte:

```text
GlobalW_t (lp.single 2 m v) n
= realCriticalPhysicalBranchIsometry m.val m.property.1 t v n.val.
```

Assim a construção global prolonga exatamente a família local anterior.

## ORTHOGONALITY ACROSS CORES

`physicalBranch_support_disjoint_of_core_ne` prova disjunção dos ranges
materiais de cores distintos, por injetividade global do endereço.

`globalCriticalPhysicalBranch_core_orthogonal` prova:

$$\langle\mathrm{GlobalW}_t(\delta_m v),
\mathrm{GlobalW}_t(\delta_l w)\rangle=0\quad(m\ne l).$$

A prova usa a isometria global e a ortogonalidade das coordenadas `lp.single`.
Não se somam vetores sobre o mesmo material; não há colisão de suportes.

## GLOBAL ISOMETRY

```lean
globalCriticalPhysicalBranchIsometry (t : ℝ) :
  CoreState →ₗᵢ[ℝ] OddMaterialState
```

- `globalCriticalPhysicalBranchIsometry_norm`:
  $\|\mathrm{GlobalW}_tV\|=\|V\|$.
- `globalCriticalPhysicalBranchIsometry_norm_sq`:

$$\|\mathrm{GlobalW}_tV\|^2=\sum_m\|V(m)\|^2.$$

A somabilidade global e Pitágoras usam a soma não negativa sobre o produto de
índices: em cada core, a soma quadrática é sua norma, pela isometria local; a
soma desses valores é finita porque `V∈CoreState`. Não se reprovou a série
geométrica do ramo nem se acrescentou normalização.

Não foi construído adjunto ou resultado de autoadjunção nesta rodada.

## PROVENANCE ROUNDTRIP

- `globalC2MaterialAddress_decode`: material → endereço → mesmo material.
- `oddMaterialC2Address_encode`: endereço → material → mesmo endereço.
- `globalC2Address_components_roundtrip`: core, sinal e depth voltam
  separadamente aos valores de entrada.
- `oddMaterialC2Address_sign`: sinal determinado pelo resíduo material.
- `oddMaterialC2Address_core`: core determinado pelo quociente explícito.
- `oddMaterialC2Address_depth`: depth é o expoente certificado do centro.
- `globalC2_provenance_roundtrip`: material e thresholds efetivos recuperados.
- `globalCriticalPhysicalBranch_zero_of_core_zero`: a coordenada depende
  somente de seu core decodificado.

A proveniência existe também para coordenadas com vetor zero; não depende de
suporte numérico não nulo nem de uma inversa escolhida.

## SEMANTIC_DIAGONAL_GAP

**PROVENANCE_GAP_CLOSED_GLOBALLY_ON_C2_ODD_MATERIAL.**

O caminho é core e depth → endereço com sinal → material → fase física.
Nenhuma igualdade identifica sample/material com depth. A source histórica
`q^n ψ_t(n)` não foi recuperada nem usada.

## GREEN READINESS — INDEX AUDIT ONLY

**GLOBAL_ODD_SOURCE_READY_FOR_GREEN_INPUT**, no nível dos tipos/índices.

`OddMaterialIndex` é um subtipo de `PNat`; portanto a extensão por zero do
setor ímpar é a inclusão natural em `ℓ²(PNat, ℝ²)` com norma euclidiana.
O tipo histórico consultado é `GreenFrame.Concrete.State := ℓ²(PNat, ℂ)`.
Para esse alinhamento de carriers restam a inclusão ímpar e o empacotamento
coordenado `ℝ² ↔ ℂ`. A inclusão mantém zero no seed e no setor par; não preenche
esses setores com uma nova source.

Nenhuma dessas duas etapas foi implementada aqui. Não se provou relação com
`concreteAnalysisOperator`, nem igualdade de sources históricas. O readiness
não é uma identificação de operadores, kernels ou frames.

## AXIOMS

37 declarações públicas novas possuem `#assert_analysis_axioms` e `#print axioms`
em `Analysis/Audit.lean`. Resultado kernel-checked:

- `PositiveOddCore`, `GlobalC2BranchAddress`, `OddMaterialIndex`,
  `oddMaterialNeighborCenter`: `[propext]`.
- Todas as demais 33 declarações, incluindo cada capstone abaixo:
  `[propext, Classical.choice, Quot.sound]`.

| Capstone | Footprint |
| --- | --- |
| `globalC2MaterialAddress_injective` | três axiomas padrão acima |
| `globalC2BranchAddressEquivOddMaterial` | três axiomas padrão acima |
| `globalC2MaterialAddress_unique` | três axiomas padrão acima |
| `globalBranchIncidenceIsometry` | três axiomas padrão acima |
| `globalCriticalPhysicalBranchIsometry` | três axiomas padrão acima |
| `globalCriticalPhysicalBranchIsometry_pointwise` | três axiomas padrão acima |
| `globalCriticalPhysicalBranchIsometry_norm_sq` | três axiomas padrão acima |
| `globalCriticalPhysicalBranch_core_orthogonal` | três axiomas padrão acima |
| `globalC2_provenance_roundtrip` | três axiomas padrão acima |
| `globalCriticalPhysicalBranch_single_core` | três axiomas padrão acima |

Nenhum axioma novo ou escape de confiança. A presença de `Classical.choice`
na dependência transitiva Mathlib não seleciona endereços na definição do
decoder. `AXIOMS.json` contém os 37 resultados individuais; o log de Analysis
preserva os outputs literais do Lean.

## BUILDS / AUDITS

Todos os checks abaixo terminaram com exit code zero no servidor `llm`:

| Check | Segundos |
| --- | ---: |
| Build isolado `Analysis.C2GlobalPhysicalBranchCanary` | 24.769 |
| Build `Analysis` | 7.053 |
| Build `Analysis.Audit` | 20.875 |
| `audit-foundation.sh` | 9.132 |
| `audit-geometry.sh` | 12.610 |
| `audit-analysis.sh` | 25.191 |
| `git diff --check` | 0.323 |
| Busca de placeholders/unsafe/axiomas | 0.330 |
| Diff vazio de Foundation, Geometry e módulos `Real*.lean` | 0.318 |

Total desta sequência de validação: **100.601 s**. Dez exemplos formais no
Audit verificam endereços 3, 5, 7, 13, inversas 3 e 13, roundtrips, unicidade,
norma e identificação do core isolado. São provas Lean, não testes numéricos.

## FILES

Novos:

- `GeometryOfNumbers/Analysis/C2GlobalPhysicalBranchCanary.lean`;
- `docs/C2_GLOBAL_PHYSICAL_BRANCH_CANARY.md`.

Modificados apenas por adições desta rodada:

- `GeometryOfNumbers/Analysis.lean`: import do novo módulo;
- `GeometryOfNumbers/Analysis/Audit.lean`: 37 guards/prints e 10 exemplos;
- `docs/SOURCE_PROVENANCE.md`: proveniência e limites semânticos.

As 18 entradas anteriores da cópia de trabalho foram verificadas por SHA256,
descontando somente as adições acima nos três arquivos compartilhados. Os
canários anteriores permanecem byte a byte intactos. Foundation, Geometry e
R2 permanecem intactos. `main`, seu HEAD e `origin/main` não foram alterados;
as alterações paralelas em `.gitignore` e `docs/HUMAN_THEORY.md` têm o mesmo
hash de patch anterior.

### Evidence bundle

Cópia local: `/home/thlinux/Downloads/FORMALIZANDO/c2_global_odd_work`.
Cópia remota: `/home/thlinux/c2-global-odd-artifacts`.

Inclui source, report, diff exclusivo desta rodada, snapshots das dependências
locais, referência Dyadic consultada, lista de declarações, `AXIOMS.json`,
`VALIDATION.json`, logs de todos os builds/audits, manifest SHA256 e verificações
de preservação. Não se sobrescreveram artefatos anteriores.

Proveniência histórica de leitura: `formalizacao_C2` HEAD
`dc35555879e3c0f188508c729c4a0ea31be246fb`, `Dyadic.lean` working SHA256
`a7b17be4ee2a41064886ef4179495aa229c3ee73da8e5028f382e9a717944c98`.
Referências `natDescendant_address_unique` e
`bracket_bijection_odd_ge_three(_exists)`; sem imports históricos.
Mathlib: `81a5d257c8e410db227a6665ed08f64fea08e997`.
GreenFrame, somente declaração de tipo: `cd2d838bee67ad23f869a02f8ed9f0a0feb926fa`.

## SEMANTIC CONCLUSION

**Sim.** As isometrias físicas dos cores C2 fixos colam sem colisões em uma
única source material real global sobre os ímpares `n≥3`. O endereço canônico
preserva core, sinal, depth e material; as duas quadraturas e a norma são
preservadas. A amplitude depende do depth e a fase do material. Nenhum
resultado adicional sobre outros setores ou camadas é afirmado.
