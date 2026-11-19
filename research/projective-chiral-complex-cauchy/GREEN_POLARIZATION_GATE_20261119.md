# Polarização refletida Green — auditoria Lean de 19/11/2026

**Escopo:** investigação do transporte entre o fechamento do bracket Genuine e a forma orientada Green. Esta nota **não** demonstra a hipótese de Riemann, positividade Hankel all-order ou simetria de um operador nativo completo.

**Proveniência:** worktree `gon-radial-cauchy-schur-20261118`, módulo `CPFormal` do CSA pinado no commit `65d50f6`. Arquivos novos revalidados com `lean -DwarningAsError=true` e `#print axioms`; apenas `propext`, `Classical.choice` e `Quot.sound`.

## 1. Polarização no próprio espaço de bordo

No tempo carry `z`, considere as duas saídas características já presentes na fonte:
```
v(z) = (z, conj(z))
w(z) = (conj(z), z)
U(z) = v(z) + i*w(z).
```
Para `omega(y,x) = conj(y_1)*x_1 - conj(y_2)*x_2`, temos exatamente

```
omega(v,v) = omega(w,w) = 0,
omega(w,v) = z^2 - conj(z)^2,
omega(U,U) = -2i*(z^2-conj(z)^2)
           = 8 Re(z) Im(z)
           = -8 Im(s) (Re(s)-1/2),  s=1/2+i*z.
```

No arquivo `ReflectedGreenPolarizationGate.lean`:

- `reflectedPolarizedFlux_green_eq_mixed`: identidade algébrica exata.
- `reflectedPolarizedFlux_green_zero_iff`: com `Re(z)≠0`, a energia assinada de `U` zera se e somente se `Im(z)=0`.
- `reflectedPolarizedValue_is_diagonal`: os **valores** de endpoint da combinação são sempre diagonais, inclusive com `Im(z)≠0`. Portanto não se pode confundir a condição sobre valores com casamento dos **fluxos**.
- `finiteCpChart_superposition`: linearidade da carta finita **com a semente, centros e pernas originais**, para toda câmera `p` e todo corte `M`.
- `polarizedNativeIntegerSample_closes_of_genuine_zero`: em zero Genuine na faixa, a superposição de duas ondas refletidas efetivamente fecha na carta finita quando `M→∞`, usando a reflexão já provada.
- `polarizedGreen_isotropy_iff_critical_at_genuine_zero`: no mesmo zero, impor a isotropia Green da superposição equivale exatamente a `Re(s)=1/2`.
- `no_isotropic_submodule_containing_reflected_pair`: para `Re(z)≠0`, `Im(z)≠0`, nenhum submódulo complexo cujos estados tenham autopa­reamento Green nulo contém os dois fluxos. A linearidade e a polarização produzem a contradição.

**Interpretação:** fechar a carta da combinação é teorema; estar num domínio Green linear isotrópico ainda não é. Fazer a segunda afirmação sem uma construção operatorial seria circular.

## 2. Contramodelo finito que testa uma passagem indevida

No arquivo `CompactBracketKernelEnergyTest.lean`, definimos a amostra

```
f(2)=2, f(3)=1, f(n)=0 em todo outro inteiro.
```

Na câmera Genuine `p=3`, a semente vale `f(1)=0` e cada segunda diferença em centros `3,6,9,...` vale zero. Portanto, para **todo M**, `finiteChart 3 M f=0`.

Entretanto, as primeiras três diferenças ordinárias são `2,-1,-1`, com energia `4+1+1=6`.

Lemas:

- `compactBracketKernelSample_chart_zero`
- `compactBracketKernelEdgeEnergy_three_eq_six`
- `no_unrestricted_C3_chart_gradient_coercivity`: não existe constante universal `C` tal que a energia das primeiras três arestas seja sempre limitada por `C*normSq(finiteChart 3 1 f)` para amostras arbitrárias.

**Limitação:** essa amostra não é `n^{-s}`, não satisfaz a equação característica nativa, nem fornece um zero Genuine fora da linha. É um *no-go* para a inferência universal **kernel da carta ⇒ ausência de energia**. A classe de ondas nativas pode ter restrições adicionais, que precisam ser demonstradas.

## 3. A correção Green Genuine não desaparece na origem

No arquivo `GreenAngularCorrectionAtZeros.lean`, especializamos o limite exato já formalizado em `CpNativeCarryAngularCorrectionExactLimit`:

```
C_M(s) = finiteCanonicalAngularGreenCorrection M s
P_∞(s) = infiniteReflectedGradientPairing s
E_∞(s) = Re(P_∞(s)) > 0.
```

Para **todo zero Genuine** na faixa:

```
C_M(s) → -P_∞(s);
Re(C_M(s)) → -E_∞(s) < 0;
eventualmente Re(C_M(s)) < -E_∞(s)/2;
C_M(s) NÃO tende a zero.
```

Esses resultados são consequências formais do limite Green e da positividade existente, sem novo teorema de localização. **Distinção crítica:** a correção acima é **não escalada**. A versão multiplicada pelo fator radial `p^d-p^{-d}` pode zerar no centro e seu fechamento, conforme a fonte, é equivalente à criticalidade.

## 4. Situação do problema principal

A tentativa de deduzir `omega(U,U)=0` somente da linearidade da carta falha como inferência universal: o contramodelo compacto possui carta nula com bulk positivo. O teorema no próprio zero Genuine prova a disponibilidade das duas ondas, mas deixa sua inclusão num mesmo domínio Green autoadjunto **sem prova**.

**Obrigação física específica:** construir, a partir do bracket com sua genealogia e do transporte TFVD/Green, uma aplicação de traço no domínio do operador nativo tal que ambas as ondas refletidas, quando fecham, pertençam a uma mesma relação linear isotrópica; provar uma identidade Green polarizada para esse traço incluindo explicitamente a correção angular e os endpoints. Não substituir o traço físico pelos pares `(z, conj z)` simplesmente por definição de domínio.

Em particular, uma estimativa universal `bulk ≤ C |carta|²` não poderá funcionar sem hipóteses adicionais. Uma próxima tentativa deve explorar uma propriedade exclusiva das soluções exponenciais nativas (e das condições de domínio/Hilbert), e não apenas a linearidade do bracket.

## 5. Reprodução

```bash
bash research/projective-chiral-complex-cauchy/validate-green-polarization.sh
```

Valida os três módulos novos no mesmo ambiente Lean/CPFormal com os diagnósticos de axiomas.
