A decomposição Green da PR #82 recupera o kernel canônico por uma forma assinada. Esta investigação formaliza a média e o contraste dos mesmos canais completos, preserva a polarização de duas entradas e demonstra que o residual de pernas iguais altera somente a média. As duas leituras comutam com o refinamento físico original.

Também certifica `J_(1/√2)>1/2` por um resto racional não negativo, com continuidade e integrabilidade provadas. Os limites separados BB/BE continuam abertos; a cota não é anunciada como sinal all-order.

O candidato `D=T C` com T simétrico tem uma condição adicional de cruzamentos. O código calcula o defeito nos estados originais e prova um NO-GO sob desigualdade explícita dos valores da resposta. Os canários numéricos violam essa condição. Isso não exclui automaticamente um operador definido apenas nos jets ou em estados-limite; tal identificação de domínios não foi provada.

- 24 teoremas; 30 raízes; 5.765 dependências de tipos/corpos; somente axiomas fundacionais permitidos.
- 14 verificações aprovadas, incluindo `--wfail` e auditorias Foundation/Geometry/Analysis.
- Experimento fornecido reproduzido: 100 pares de câmeras, pivôs por divisores e níveis, perfis Green e seis pivôs positivos da Jacobi decimal fornecida. Nenhuma identidade com a Hankel infinita é inferida desses testes.

**PARTIAL.** Próximo passo mínimo: identificar exatamente o termo misto do Green em escala finita e só depois passar ao limite. Relatório A–E em `research/mean-contrast-green/REPORT.md`.

Base: PR #82, `79e43c991251a1219ec8c1b1901863f67d3a1d1a`. PR #41 preservada como draft independente. Draft, sem merge automático; fontes, métricas, pesos e pins mantidos.
