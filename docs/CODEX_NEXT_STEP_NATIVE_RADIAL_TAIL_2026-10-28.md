# Prompt para Codex — próximo gate quantitativo após consolidação #34–#133

> Copiar a seção abaixo integralmente para o Codex. **Uma única tarefa matemática, sem reconstruir o que já está formalizado.**

---

Você vai trabalhar no repositório \`thiagomassensini/geometry-of-numbers\`, a partir do **main atual**. Os PRs #34–#133 já foram consolidados/mergeados; não use como base um branch antigo nem refaça os merges. Leia primeiro o README e \`docs/HANDOFF_POSITIVIDADE_LOG_GREEN_2026-10-28.md\`. Depois leia integralmente os relatórios e as declarações Lean relevantes de:

- \`research/native-stencil-integrated-control/REPORT.md\` (PR #133);
- \`research/native-jet-variation-budget/REPORT.md\` (PR #132);
- \`research/native-all-order-radial-tail/REPORT.md\` (PR #131);
- \`research/native-effective-radial-budget/REPORT.md\` (PR #130);
- \`research/native-boundary-euler-reconstruction/REPORT.md\` (PR #129);
- \`research/structural-native-krylov-gap/REPORT.md\` (PR #36);
- \`research/native-moment-orthogonalization-audit/REPORT.md\` (PR #41);
- \`research/mean-contrast-green/REPORT.md\` (PR #83).

Se a prova exigir uma API do operador, consulte \`carry-self-adjoint-operator\` e \`green-frame-theorem\` nos **pins efetivamente usados**, sem atualizá-los arbitrariamente.

## Objetivo único

**Fechar o orçamento somável de incrementos radiais para uma combinação finita arbitrária de jets ímpares da fonte nativa original**, generalizando a parte *orçamento de cauda* da PR #130, mas **sem** alegar positividade canônica all-order.

A PR #133 já provou \`integrated_native_grid_jets_unconditional\` e a identidade all-order \`odd_stencil_correction_all_order\`, além do transporte físico completo com \`-Lambda_{m,n}\`. Falta transformar o integral de erro entre passos em **uma estimativa explícita e somável** para a mesma forma física, com constantes e limiar verificáveis, para cada dimensão finita fixa.

Prove preferencialmente um enunciado do tipo (adapte aos nomes e normalizações REAIS do código):

\`\`\`text
para N finito, ordens ímpares finitas e coeficientes c fixos,
existe K explícito e um majorante computável E(N,c,K) ≥ 0,
com E(N,c,K) → 0 quando K → ∞,
tal que
  Σ_{j≥K} |D_j(c) - D_{j+1}(c)| ≤ E(N,c,K).
\`\`\`

Aqui \`D_j(c)\` **deve ser exatamente** o pareamento/energia nativa completada já existente, com os dois canais físicos, ambas as pernas, retorno, bordos, 9/36 cruzamentos quando aplicável, amplitude, fases e resto analítico. Não crie uma forma substituta positiva. Se for necessário, enuncie primeiro a versão **polarizada** em duas famílias finitas independentes, depois especialize à diagonal.

### Rota técnica preferencial

1. Use \`original_odd_pair_expansion_lambda\`, \`original_finite_odd_energy_correction_lambda\`, \`integrated_native_grid_jets_unconditional\`, \`native_jet_velocity_size\` e as cotas de resto/derivada de #130–132. Não reprove a identidade combinatória \`Lambda\`.
2. Para cada família finita fixa, procure uma expansão física diferenciável \`D_c(h)=D_c(0)+C_c h²+h⁴ R_c(h)\` **somente se** ela for consequência da resposta e da normalização originais. Controle \`|C_c|\`, \`|R_c(h)|\` e \`|R_c'(h)|\` com constantes efetivas; o majorante de coeficientes \`|h_n|≤(22/175)^{n+1}\` pode ser usado apenas como cota de magnitude já provada, nunca como lei de sinal.
3. Se essa expansão for provada, a estimativa \`|D'_c(h)|≤2|C_c|h+4M h³+M' h⁴\` permite integrar entre \`h_{k+1}\` e \`h_k\` e somar telescopicamente. Obtenha uma expressão explícita \`E(N,c,K)\` em potências de \`h_K=1/(K+1)\`. **Verifique os fatores e a normalização contra os teoremas Lean reais**.
4. Se a cota ingênua dos módulos dos stencils divergir por fatores \`m/h\`, não a esconda. Extraia primeiro os cancelamentos binomiais/Euler–Newton **na forma completada**, antes de aplicar desigualdade triangular. Um NO-GO de majorante bruto é um resultado legítimo, mas identifique exatamente o termo responsável.
5. Regressão obrigatória: especialize ao caso de seis endereços da PR #130, onde já existem \`K=10^20-1\`, \`D_K>10^-16\` e cauda \`≤10^-40\`. Não substitua nem enfraqueça o certificado antigo; use-o como controle de coerência.

### Proibições e critérios de aceitação

- Não pressupor RH, zeros, alturas, positividade Hankel, pivôs positivos, uma Gram canônica ou uma fonte construída a partir dos momentos.
- A PR #36 **refutou** a identificação \`h_n=⟨v,L^{2n}v⟩\` para o clock material original; não tente vendê-la como ponte nova. O operador \`log n\` e seu transporte Green **já estão formalizados**; reutilize-os somente quando a identidade tipada for pertinente.
- A PR #83 mostra que média–contraste não impõe \`T≥0\` automaticamente. A PR #132 dá um contraexemplo de dois átomos ao sinal da correção; a PR #133 prova \`Lambda>0\` por entrada mas a matriz de coeficientes tem direção negativa. Não inferir positividade de sinais locais.
- Não mudar fonte, pesos, \`sigma\`, câmera, métrica, dressing, Gamma, amplitude, fatoriais, \`lean-toolchain\`, \`lakefile.toml\`, pins ou operadores para fazer o resultado passar.
- Prova Lean sem \`sorry\`, \`admit\`, axiomas novos ou dependência oculta de certificados de sinal posteriores. \`#print axioms\` e auditoria transitiva de tipos/corpos; só axiomas padrão permitidos.
- Criar branch novo e PR; não empilhar em branches já mergeados. Entregar módulo(s) pequenos, \`REPORT.md\` em A–E com teoremas exatos, o que foi refutado, limites e comandos reprodutíveis. Rodar \`lake build --wfail\` e auditorias Foundation/Geometry/Analysis, além dos módulos de pesquisa relevantes com dependências originais.
- Se o gate quantitativo não fechar, relatar **a menor obrigação matemática exata que bloqueou** e um contraexemplo se houver. Não apresentar um teorema condicional com a desigualdade desejada como se fosse prova do sinal.

### Próximo gate, mas **não** incluído como sucesso desta tarefa

Uma vez provada a cauda explícita, buscar uma desigualdade **independente** que certifique, na mesma escala e para a mesma direção física crítica, \`D_K(c)>E(N,c,K)\`. Isso seria a origem do sinal. A PR #130 o fez apenas para uma direção de seis endereços; não extrapolar para todas as ordens.

**Entregue primeiro a formulação Lean precisa do teorema-alvo e um plano curto de dependências. Depois implemente. Não desperdice contexto tentando resolver de uma vez a positividade Hankel em toda ordem.**
