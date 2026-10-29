O cruzamento Green do jet zero tinha uma fórmula numérica e um orçamento J positivo, mas sua identificação com a fonte original ainda não estava provada. Esta PR deriva o numerador TFVD completo para e0, conserva os dois bordos no bulk e identifica vetorialmente o residual reconstruído com a ação do resolvente físico original.

O integral J é agora exatamente o overlap da coluna física zero com a porta Green original. Daí seguem a fórmula complexa finita `Phi(B,E)=-i kappa deltaR J` e os limites separados `BE→h0 J`, `BB→h0(1−2J)`, sem hipótese de sinal nessa construção.

Com `J_(1/√2)>1/2` da PR83 e o certificado antigo de h0>0, demonstra-se que eventualmente o bulk C2 é negativo e o misto duplo o compensa estritamente. A origem theta/baixa ordem do certificado antigo fica explícita; não se anuncia uma nova lei geométrica all-order.

- 48 teoremas e seis definições; 54 raízes públicas; 6.079 dependências de tipos/corpos; somente axiomas fundacionais permitidos.
- Auditorias separadas de construção sem momentos, identificação analítica e orientação por h0.
- 17 verificações aprovadas, incluindo `--wfail`, auditorias Foundation/Geometry/Analysis, regressão Green 80/120 dígitos e revisão independente do novo contexto centro–pernas.

**PARTIAL global; alvo finito da PR83 cumprido.** A próxima obrigação é extrair e1 e seus cruzamentos com e0, antes de montar a diferença finita normalizada do primeiro jet ímpar. Relatório A–E em `research/finite-green-crossing/REPORT.md`.

Base: PR #83, `a2b8aeadff77c0be17a09263a0e188f1c57a46d4`. PR #41 preservada como draft independente. Sem merge automático; fontes, métricas, amplitudes e pins mantidos.
