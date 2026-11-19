# Transporte TFVD do pareamento Green refletido — checkpoint 19/11/2026

**Proveniência:** geometry-of-numbers, PR #344, branch `research/radial-cauchy-schur-all-orders-20261118`. Fonte CPFormal fixada no CSA em `65d50f6`. O cálculo começa no bracket local de centros e pernas C3, passa pela carta Genuine com semente, pelos gradientes Dirichlet nativos e pela reconstrução TFVD já formalizada. Não confundir este Green *bulk* de gradientes com a forma Green orientada dos endpoints `nativeCarryReflectedLogBoundaryForm`.

## 1. Transporte misto finito, sem escolha de domínio

O módulo `TfvdMixedGreenExactTransport.lean` usa as duas sequências **originais** de arestas `positiveDirichletGradient s n` e `positiveDirichletGradient (reflectedParameter s) n`. Elas são recortadas no core finito pelo produtor existente `c2DirichletGradientPrefixCore`, incorporadas em `CarryVerticalL2`, analisadas via `nativeGpreFiniteTfvdAnalysis q S` e reconstruídas por `nativeGpreFiniteTfvdReconstruction q`.

Para toda câmera de análise TFVD `0<q<1`, todo atlas finito `S`, todo parâmetro `s` e todo `N`:

```
TFVD_Mixed(N,s)
 = ∑_{n<N} conj(Rec(Analysis(x_s))(n)) * Rec(Analysis(x_s#))(n)
 = finiteReflectedGradientPairing N s.
```

O teorema é `tfvdReconstructedReflectedGradientPairing_eq`. É igualdade finita **exata**, antes do limite, e não requer `genuineContinuation s=0`.

A positividade estrita (`Re TFVD_Mixed(N,s)>0`, quando `N>0` e `s` pertence à faixa Genuine) e o limite para `E_∞(s)>0` são transportados sem perda.

## 2. O defeito angular não desaparece ao reconstruir

A identidade finita com *seed*, centro, pernas e correção angular preservados é:

```
finiteCanonicalAngularScalarPairing M s
  = TFVD_Mixed(3M,s)
  + finiteCanonicalAngularGreenCorrection M s.
```

Teorema `finiteCanonicalAngularScalarPairing_eq_tfvd_mixed_add_correction`. A origem é a identidade `finiteCanonicalAngularScalarPairing_eq_green_add_correction`, já provada no CPFormal, agora substituindo exatamente a energia reconstruída pelo TFVD.

Em qualquer zero Genuine `s` na faixa:

```
Scalar_M(s) → 0,
TFVD_Mixed(3M,s) → P_∞(s) ≠ 0,
Re P_∞(s) = E_∞(s) > 0,
Correction_M(s) → -P_∞(s),
TFVD_Mixed(3M,s) + Correction_M(s) → 0.
```

Formalizações:

- `genuine_zero_tfvd_mixed_green_survival` prova lado escalar e positividade do limite.
- `genuine_zero_tfvd_mixed_green_not_tendsto_zero` prova que o bulk reconstruído não converge a zero.
- `genuine_zero_tfvd_mixed_green_full_ledger_tendsto_zero` prova o fechamento do **total**, não das parcelas isoladas.

**Significado:** a análise TFVD é fiel. O fechamento escalar Genuine ocorre por cancelamento de bulk positivo com correção não escalada negativa, não por anulação de cada energia. Não há como apagar o defeito por uma mudança de representação linear invertível.

## 3. Contramodelo na própria reconstrução TFVD

Em `CompactBracketKernelEnergyTest.lean`, temos a amostra de suporte finito:

```
f(1)=0, f(2)=2, f(3)=1, f(n)=0 nos demais n.
```

Os brackets C3 locais são zero em todos os centros `3,6,9,...`, e a semente é zero, logo `finiteChart 3 M f=0` para **todo** `M`.

O novo core TFVD `compactC3KernelGradientCore` contém exatamente as três primeiras diferenças consecutivas `(2,-1,-1)`. O teorema `compactC3KernelGradientCore_eq_sample_differences` verifica as coordenadas. Para todo `0<q<1` e atlas `S`, `compactC3Kernel_tfvd_no_scalar_energy_collapse` certifica simultaneamente:

```
∀ M, finiteChart 3 M f=0;
∑_{n<3} normSq(Rec(Analysis(grad f))(n)) = 6.
```

Este é um **contramodelo da inferência universal** `fechamento escalar ⇒ energia reconstruída nula`, mesmo com a reconstrução TFVD exata e com a verdadeira carta C3. Não é uma onda espectral `n^{-s}` e não contradiz localização de zeros nem a possibilidade de um vínculo mais restrito de domínio para as ondas genuínas.

## 4. A obrigação realmente restante

A forma de bordo `nativeCarryReflectedLogBoundaryForm` é **outro objeto**: `ω(y,x)=conj(y₁)x₁ - conj(y₂)x₂`, sobre valores/fluxos refletidos. Na superposição das duas ondas em um zero Genuine, a isotropia da forma orientada equivale à meia abscissa; isso consta no módulo `ReflectedGreenPolarizationGate.lean`.

Os novos resultados TFVD **não demonstram** que o par de fluxos dos endpoints pertença à mesma relação autoadjunta. Mostram que a passagem pelas arestas preserva a informação necessária, mas traz junto uma correção não nula.

Próxima obrigação de fato não circular:

1. Definir a aplicação de traço **física** da onda reconstruída, não um par `(z,conj z)` atribuído artificialmente.
2. Derivar sua identidade de Green orientada **polarizada**, transportando a correção angular e o endpoint junto com a semente, sem perder o termo de bulk.
3. Mostrar por que o domínio admissível original impõe isotropia às **duas ondas** que fecham no bracket. A condição de domínio deve vir de hipóteses comprováveis independentemente da localização de zeros.
4. Verificar a interface `CpTfvdGpreCollapseInterface`. O módulo `CpTfvdSameEdgeReflectedEnergyFixedTimeNoGo` já impede usar sem compensação a energia refletida bruta como fonte de momento nativo em tempo fixo, mesmo no centro.

O passo (3) é a peça que falta; não foi transformado num axioma nem num argumento circular.

## 5. Auditoria

Reproduzir na VM:

```bash
bash research/projective-chiral-complex-cauchy/validate-green-polarization.sh
```

O script confere o pin CPFormal `65d50f6`, compila os quatro módulos com `lean -DwarningAsError=true` e rejeita `sorryAx`/erros. Nos novos teoremas, `#print axioms` relata apenas `propext`, `Classical.choice` e `Quot.sound`.
