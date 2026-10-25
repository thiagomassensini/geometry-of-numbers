A PR #89 isolou a limitação afim do Pitágoras com readouts fixos. Esta continuação constrói o projetor linear por atlas primo com readouts dependentes do estado, preservando pareamentos polarizados, ambas as quadraturas e a cauda do atlas. O transporte nativo G_pre→primos existente é reutilizado.

Foi demonstrada uma porta física finita: para as features Cauchy originais F_c(u)=sqrt(u)[c0+uD_c(u)], a integral Mellin de D_c até 1/p é exatamente o perfil p^(-j)/j da análise prima. O trace c0 permanece separado; as duas quadraturas são sintetizadas como vetores contínuos antes da passagem a L².

A comparação não fecha uma Gram positiva canônica. Calcula o defeito de kernel, inclusive no multiplicador quiral completado, e prova dois NO-GOs locais: a câmera 2 lê energia 1/2 da primeira coluna não constante, cuja energia física é 1/4; e a análise prima com margem fixa 11/12 não pode coincidir isometricamente com o retorno nativo, cuja razão de energias tende a 1. Nenhum peso ou métrica foi ajustado.

**Resultado: PARTIAL.** Sem hipótese de positividade canônica. A extensão da porta ao domínio completo e o transporte exato até a Hankel continuam abertos. Próximo teste: admissibilidade/fechabilidade da porta Mellin no domínio nativo, com os bordos retidos.

A auditoria paralela da campanha `momentos/native_jet_exploration/vm_campaign` conferiu 3 hashes arquivados e 64 momentos canônicos com 313 dígitos relativos comuns, sem nova campanha ou solução espectral. É regressão finita, não prova de sinal ou ponte geométrica.

Validação: 67 teoremas novos, 79 declarações públicas e 5731 dependências auditadas; 18 comandos aprovados. Módulos novos compilados explicitamente com warningAsError, `lake build --wfail`, auditorias Foundation/Geometry/Analysis, `#print axioms` e caminhada transitiva de tipos/corpos com guard contra dependência dos momentos canônicos. Comandos e evidências em `research/source-dependent-prime-readouts/evidence/`; relatório A–E em português em `REPORT.md`.

Base: PR #89, commit d17aba9dfd0aa53a7b677cbb3da0e1e6213e0a54. Somente nova pasta de pesquisa. Draft, sem merge automático. Fontes, pins e alterações preexistentes nos três repositórios preservados.
