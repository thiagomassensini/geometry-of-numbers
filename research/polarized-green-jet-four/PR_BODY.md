A PR #87 extraiu a parte finita de `J₂−aJ₀`. Esta continuação demonstra a expansão do balanço Green original para dois vetores independentes em `span(J₀,J₂,J₄)`:

`Eₖ(c,d)=P(c,d)+κ⁻² C(c,d)+κ⁻⁴ Q(c,d)+O(κ⁻⁶)`.

A parte finita é exatamente a funcional original `L_h(p_c p_d)`. As duas matrizes de correção são explícitas, envolvendo os momentos canônicos até h₆. O resto analítico é retido e limitado. A identidade complexa de Green conserva BB/BE/EB/EE antes do readout real; os 25 cruzamentos ordenados e as duas pernas permanecem.

O transporte crítico reutiliza diretamente o lema da PR #41 com `IsUnit` do prefixo antigo. Obtém-se o mesmo Schur e a ortogonalidade a todo o espaço antigo no limite, sem receber o sinal do novo pivô. Cinco regressões Lean reproduzem exatamente a entrada, o balanço e os coeficientes da PR #87 quando c₂=d₂=0.

Validação: seis módulos Lean novos e auditoria explícita com avisos tratados como erros, `lake build --wfail` focado/raiz, auditorias Foundation/Geometry/Analysis, inspeção transitiva de tipos/corpos e `#print axioms`, diagnóstico físico a 80/120 dígitos. Relatório em português, logs e hashes em `research/polarized-green-jet-four/`.

A lei candidata para os pesos binomiais da primeira correção foi testada em 25 pares racionais finitos, sem momentos como entradas. Esse canário da próxima obrigação está separado das provas Lean; não é uma lei all-order formalizada.

Base: PR #87, commit `16caee18d2667dc54ab6fdb37750c136b2366b06`. Resultado PARTIAL. Não se afirma positividade do kernel assinado, novo sinal dos coeficientes críticos, uniformidade na ordem ou uma representação Gram positiva infinita. Draft, sem merge automático; fontes, pins, métricas e PRs anteriores preservados.
