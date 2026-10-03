> Recuperação canônica de 3 de outubro de 2026: fonte e status históricos preservados abaixo.
> Os caminhos antigos e frases sem commit/push descrevem a execução original.
> A versão atual vive em `GeometryOfNumbers/Analysis`; ver `RECOVERY_2026-10-02.md`.

# Ledger Green por câmera: contribuição exata da base 2

## STATUS

**PASS — on the provenance-correct odd C2 source, the direct base-two Green channel vanishes while the vertical stencil creates an explicit strictly positive diagonal energy; any global raw isometry would therefore require exact negative compensation from the non-base-two cameras.**

A positividade é para entrada não nula. Nenhum resultado desta rodada exclui o cancelamento global nem conclui que o Gram restrito seja diferente da identidade.

## Repositório e convenções

- Worktree no servidor `llm`: `/home/thlinux/carry-c2-source-raw-green`.
- Branch: `canary-c2-source-raw-green`.
- HEAD mantido: `cb33c845a7ee0ca1c6bf195d34d7f3ac1628edfa`.
- Módulos anteriores consumidos sem editar: `C2GlobalGreenBridge.lean` e `C2GreenPreStencilCanary.lean`.
- GreenFrame consultado: commit `cd2d838bee67ad23f869a02f8ed9f0a0feb926fa`.
- Namespace novo: `CarrySelfAdjointOperator.C2BaseTwoGreenLedger`.
- Neste relatório, `f_t := c2GlobalGreenInputIsometry t V`, `ω₂(n) := carryCameraWeight 2 n` e `q₂ := carryRatio 0`.

Nenhuma alteração em `geometry-of-numbers`, R2, GreenFrame ou nos canários anteriores. Não houve commit, merge ou push. Hashes e estados estão nas evidências de preservação.

## BASE TWO CODE

**Código = 0.** A API define `baseNat r := r + 2`.

Teoremas novos:

- `baseTwo_code`: `baseNat 0 = 2`;
- `baseTwo_positive_code`: `basePNat 0 = 2`;
- `baseTwo_real_code`: `baseReal 0 = 2`;
- `carryRatio_baseTwo_sq`: `carryRatio 0 ^ 2 = 1/2`, por especialização do resultado existente `carryRatio_sq_eq_one_div`.

`baseTwoGreenProjection` e `nonBaseTwoGreenProjection` são os `l2CoordinateMaskCLM` existentes, com os predicados `e.1 = 0` e `e.1 ≠ 0`. São mapas contínuos complexos lineares em `ℓ²(GreenEvent, ℂ)`, idempotentes e auto-adjuntos. Esses fatos foram obtidos diretamente da API de máscaras, sem nova construção de adjoint.

## ODD SUPPORT

A source é a já provada, com suporte em `OddMaterialIndex = {n : PNat // Odd n ∧ 3 ≤ n}`.

Reutilizados `c2GlobalGreenInput_one`, `c2GlobalGreenInput_even` e a fórmula material da source. O novo lema conveniente é:

```lean
c2GlobalGreenInput_even_eq_zero
```

$$f_t(2p)=0\qquad(p:\mathrm{PNat}).$$

A fase continua sendo a rotação física em `−t log n`. A amplitude continua determinada pela profundidade do endereço C2, sem substituição por uma potência do índice material.

## DIRECT BASE-TWO

**Pointwise** — `directGreenCoordinate_baseTwo_c2Source_eq_zero`:

$$D_{(0,p)}(f_t)=\sqrt{\omega_2(2p)/2}\,f_t(2p)=0.$$

**Global** — `baseTwo_directGreenAnalysis_c2Source_eq_zero`:

$$P_2 D(f_t)=0.$$

Logo a energia direta da câmera 2 é exatamente zero. Não é uma estimativa de pequeno erro.

## STENCIL / ODD PARENT

`verticalGreenStencil_baseTwo_oddParent`, para `p` ímpar positivo:

$$\boxed{S_2(f_t;p)=-2q_2f_t(p).}$$

Aqui `current = 2p` é par e não há segundo ancestral, pois `2 ∤ p`.

## STENCIL / TWICE-ODD PARENT

`grandparentIndex_baseTwo_twice` recupera exatamente `p` do parent `2p`.

`verticalGreenStencil_baseTwo_twiceParent` vale para todo `p` positivo; sua especialização `verticalGreenStencil_baseTwo_twiceOddParent` dá:

$$\boxed{S_2(f_t;2p)=q_2^2f_t(p)=\tfrac12f_t(p).}$$

Os valores corrente `f_t(4p)` e parent `f_t(2p)` zeram.

## DEEPER EVENTS

`verticalGreenStencil_baseTwo_parent_four_dvd_eq_zero`:

$$4\mid parent\Longrightarrow S_2(f_t;parent)=0.$$

`baseTwoGreen_c2Source_eq_zero_off_generations` é o controle de suporte completo do setor mascarado, incluindo os rows dos parents `1` e `2`, que zeram pelo seed.

As únicas famílias potencialmente não nulas são:

```text
(0,p)   : current 2p, p ímpar ≥3
(0,2p)  : current 4p, p ímpar ≥3
```

`baseTwoGenerationEvent : OddMaterialIndex ⊕ OddMaterialIndex → GreenEvent` enumera essas famílias explicitamente. `baseTwoGenerationEvent_injective` prova ausência de colisões. Não há enumeração por choice.

**Distinção de profundidades:** as gerações Green de profundidade 1 e 2 são as torres de raiz ímpar `p`. Não se identificam com a profundidade C2 recuperada do endereço que gerou a coordenada material `f_t(p)`.

## WEIGHT POSITIVITY

Provas exatas:

- `positionalDepth_two_two_mul_odd`: `positionalDepth 2 (2p) = 1`;
- `positionalDepth_two_four_mul_odd`: `positionalDepth 2 (4p) = 2`;
- `allBaseActivity_two_two_mul_odd`: `allBaseActivity 2 (2p) = log 2`;
- `carryCameraWeight_two_two_mul_odd_pos`: `ω₂(2p) > 0`;
- `carryCameraWeight_two_four_mul_odd_pos`: `ω₂(4p) > 0`.

A positividade usa atividade log-depth positiva e o normalizador positivo já provado. Não se introduziu fórmula aproximada ou peso alternativo.

## FIRST-GENERATION ENERGY

`baseTwo_firstGeneration_greenCoordinate_normSq`:

$$\boxed{|G_{(0,p)}(f_t)|^2=\omega_2(2p)|f_t(p)|^2.}$$

O fator `ω₂(2p)/2` da massa transmitida multiplica `4q₂²|f_t(p)|² = 2|f_t(p)|²`.

## SECOND-GENERATION ENERGY

`baseTwo_secondGeneration_greenCoordinate_normSq`:

$$\boxed{|G_{(0,2p)}(f_t)|^2=\frac{\omega_2(4p)}8|f_t(p)|^2.}$$

O fator `ω₂(4p)/2` multiplica `|f_t(p)/2|²`.

## BASE-TWO TOTAL ENERGY

Defina a diagonal explícita já formalizada:

$$\alpha(p)=\omega_2(2p)+\frac{\omega_2(4p)}8.$$

`baseTwoOddDiagonalWeight` é literalmente essa expressão, e `baseTwoOddDiagonalWeight_pos` prova `α(p)>0` em todo `OddMaterialIndex`.

Capstone `baseTwoGreenStencilEnergy_eq_odd_diagonal`:

$$\boxed{\|P_2G(f_t)\|^2=
\sum_{p\in\mathrm{OddMaterialIndex}}\alpha(p)|f_t(p)|^2.}$$

A prova usa somabilidade dos norm-squares em ℓ², a reindexação injetiva `baseTwoGenerationEvent`, o controle de suporte completo e a decomposição da soma sobre um tipo soma. Cada parcela é substituída pela energia pontual provada acima. Não há truncamento ou conta numérica.

Uma opção local de transparência de elaboração é usada somente neste teorema para resolver as coerções de ℓ² e instâncias durante a reindexação. A prova produz termo Lean kernel-checked; não modifica o footprint de confiança.

## STRICT POSITIVITY

`c2GlobalGreenInput_exists_nonzero_odd_coordinate` recupera uma coordenada material não nula de qualquer source não nula, usando seu suporte real existente.

`baseTwoGreenStencilEnergy_pos_of_c2Source_ne_zero`:

$$f_t\ne0\Longrightarrow\|P_2G(f_t)\|^2>0.$$

A prova utiliza uma parcela estritamente positiva e seu limite superior pelo tsum não negativo. A injetividade da isometria da source dá:

`baseTwoGreenStencilEnergy_pos_of_core_ne_zero`:

$$V\ne0\Longrightarrow\|P_2G(f_t)\|^2>0.$$

Assim o vetor de stencil da câmera 2 também é não nulo para entrada não nula. Não se afirma que cada row seja não nulo quando sua coordenada de entrada zera.

## BASE-TWO DEFECT

```lean
baseTwoDefect t V := ‖P₂ G(f_t)‖² - ‖P₂ D(f_t)‖²
```

`baseTwoDefect_eq_stencilEnergy` e `baseTwoDefect_pos`:

$$\boxed{D_{2,t}(V)=\|P_2G(f_t)\|^2,
\qquad V\ne0\Longrightarrow D_{2,t}(V)>0.}$$

Este é o excesso estritamente positivo obrigatório da câmera 2 sobre a source autorizada.

## NON-BASE-TWO REMAINDER

```lean
nonBaseTwoDefect t V := ‖P≠₂ G(f_t)‖² - ‖P≠₂ D(f_t)‖²
```

`baseTwo_nonBaseTwo_norm_sq_add` é Pitágoras para as duas máscaras ortogonais.

Com a identidade do canário pré-stencil anterior, `c2GlobalRawGreenDefect_eq_camera_ledger` prova:

$$\boxed{D_t(V)=D_{2,t}(V)+D_{\ne2,t}(V).}$$

Não há conclusão incondicional sobre o sinal do segundo termo.

## CANCELLATION GATE

`restrictedGram_eq_identity_implies_nonBaseTwo_exact_cancellation`:

$$\boxed{G_t=I\Longrightarrow
D_{\ne2,t}(V)=-D_{2,t}(V)\quad\text{para todo }V.}$$

`restrictedGram_eq_identity_implies_nonBaseTwo_negative`:

$$G_t=I\ \land\ V\ne0\Longrightarrow D_{\ne2,t}(V)<0.$$

É uma condição sobre a contribuição **agregada** das câmeras não-base-2. Não impõe negatividade separada a cada câmera. Não prova que o cancelamento seja impossível.

## TIME DEPENDENCE

**Independente de `t`: YES.**

`c2GlobalGreenInput_normSq_independent_time` é obtido por composição da fórmula material existente, do packaging de energia e dos teoremas reais `scaleRealPlane_energy` / `rotateRealPlane_energy`.

Substituindo essa igualdade na soma diagonal, `baseTwoDefect_independent_time` prova:

$$\boxed{D_{2,t}(V)=D_{2,s}(V)\qquad(t,s\in\mathbb R).}$$

Não se introduziu representação de Euler complexa para demonstrar invariância de energia.

## AXIOMS / validação

- 47 declarações públicas novas guardadas e impressas pelo audit dedicado.
- Footprint máximo: `[propext, Classical.choice, Quot.sound]`. Algumas declarações elementares têm footprint menor ou vazio.
- Módulo principal: build remoto PASS.
- Audit: build remoto PASS e reexecução direta pelo Lean PASS.
- `git diff --check`: PASS.
- Código novo sem `sorry`, `admit`, declarações `axiom` ou `unsafe`; sem whitening e sem afirmação de não identidade do Gram global.
- Audit textual global: mantém a falha herdada por cinco matches em comentários antigos. Comparação com HEAD: mesmos cinco matches, sem acréscimos. Não foram alterados os módulos antigos para silenciar o script.
- Arquivos de trabalho anteriores e fontes upstream preservados por comparação de hashes/estado.

Evidências: `AXIOMS.json`, `PUBLIC_NAMES.json`, `VALIDATION.json`, `SOURCE_MANIFEST.json`, `PRESERVATION_BEFORE.json`, `PRESERVATION_AFTER.json` e `logs/` no bundle da rodada.

## FILES

Apenas três arquivos novos na worktree:

1. `CarrySelfAdjointOperator/C2BaseTwoGreenLedger.lean`;
2. `CarrySelfAdjointOperator/C2BaseTwoGreenLedgerAudit.lean`;
3. `docs/C2_BASE_TWO_GREEN_LEDGER.md`.

Bundle local: `/home/thlinux/Downloads/FORMALIZANDO/c2_base_two_work`.

## SEMANTIC CONCLUSION

**Sim.** Sobre a source global C2 ímpar correta, a câmera base 2 tem canal Green direto nulo e cria pelo stencil uma energia diagonal explícita, estritamente positiva em toda entrada não nula e independente de `t`.

Qualquer eventual identidade global do Gram bruto exigiria compensação negativa agregada **exatamente igual** a esse excesso pelas demais câmeras. A possibilidade dessa compensação permanece aberta nesta rodada. Nenhuma normalização de métrica ou conclusão espectral foi usada.
