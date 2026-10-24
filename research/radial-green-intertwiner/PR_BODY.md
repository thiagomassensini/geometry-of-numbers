O avanço e o Green originais agora são compatíveis com o refinamento isométrico da PR #81: `Uθ A=A^θ Uθ` e `Uθ G₁=Gθ Uθ`. O resolvente foi identificado com o `physicalGreenResolvent` existente, com invertibilidade provada no domínio válido.

A reconstrução TFVD completa conserva os dois bordos e o numerador residual. Seu pareamento de duas entradas é exatamente o kernel canônico. A igualdade preexistente das pernas do residual foi propagada pelo Green refinado: o setor RR anula-se exatamente na seção regular; BE e EB permanecem.

Também foi provada uma obstrução de domínio: o resolvente da primeira coluna não pertence ao span finito. A síntese **completa e corrigida** volta ao domínio, com testemunho único e readout material covariante, sem criar uma funcional em todo Lp.

- 58 teoremas, 79 raízes, 5.943 dependências de tipos/corpos; somente axiomas fundacionais permitidos. Construção sem momentos ou sinais canônicos como entrada.
- 18 verificações aprovadas, incluindo `--wfail`, auditorias e um diagnóstico Python separado.
- No canário original em η=1/√2, o bulk ficou numericamente negativo e o misto compensador positivo já no jet zero. Isso é diagnóstico, não um novo sinal certificado em Lean.

**PASS_STRUCTURAL / PARTIAL global.** A positividade all-order continua aberta: a reconstrução não é uma prova independente de passividade. Próximo teste: formalizar o limite misto observado, depois controlar o residual nativo/Gamma sem pressupor o pivô.

Base: PR #81, `ee6301bf05e59a246d3d8f7e1d4d1bb482a4f57d`. Relatório A–E e evidências em `research/radial-green-intertwiner/`. Draft, sem merge automático.
