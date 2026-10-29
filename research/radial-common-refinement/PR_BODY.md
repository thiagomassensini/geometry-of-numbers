A PR #80 mostrou que cruzamentos radiais brutos não colam: o fator misto não desaparece no limite. Esta PR constrói uma mudança de coordenadas literal no mesmo carrier Cauchy físico, com raiz do Jacobiano de `x↦x^θ`, e prova sua isometria antes de usar momentos.

As duas representações são transportadas a uma grade comum por isometrias distintas e coerentes por composição. O pareamento assinado dos canais originais passa a coincidir exatamente com o kernel nativo em dois argumentos; todos os jets conjuntos recuperam `h_(i+j)`, `h_(i+j+1)` e os zeros de paridade mista. Não se divide um kernel por um fator ajustado.

- Domínio finito, ação Euler, seis campos da fonte, quatro cruzamentos Green/completion e cabeça/cauda preservados.
- A leitura Dirichlet é covariante: o fator `√θ θ^(-s)` permanece, com módulo 1 na linha crítica. Não se afirma invariância literal do estado material.
- 51 teoremas; 69 raízes com auditoria de 6.238 dependências de tipos/corpos. Construção sem momentos, identificação posterior sem sinais finitos.
- 17 verificações aprovadas: módulos explícitos, `--wfail`, auditorias Foundation/Geometry/Analysis. Sem axiomas novos ou escapes.

**PASS_STRUCTURAL radial / PARTIAL global.** O balanço ainda é assinado; positividade all-order e o transporte dinâmico material completo continuam abertos. Próxima obrigação: intertwiner do avanço/Green original com essas isometrias, seguido da identificação do readout completado.

Base: PR #80, `0618317827981136657cb1b5bb728a8e93cea50d`. Relatório A–E em português e avaliação da nota centro–pernas em `research/radial-common-refinement/REPORT.md`. Draft, sem merge automático.
