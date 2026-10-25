A partir do endereço 2, o numerador TFVD mantém um residual anterior além do avanço do residual atual. Esta continuação extrai a porta original para todo endereço interior e fecha a síntese residual vetorial de qualquer entrada complexa finita, com as duas exceções de bordo preservadas.

O transporte para J₂−aJ₀ conserva o fatorial, a fase, os nove cruzamentos e dois argumentos radiais independentes. O limite polarizado é h₂−(a+b)h₁+ab h₀; com a=b=h₁/h₀ e apenas h₀≠0, o balanço Green completo converge para a definição original sourceMomentSchur h 0 1, usada pela PR #41. Não se recebe o sinal desse pivô nem se constrói uma Gram substituta.

Classificação PARTIAL: as portas e o mesmo residual estão identificados, mas a desigualdade independente que determine o sinal em toda ordem permanece aberta. O experimento a 80/120 dígitos é diagnóstico e não substitui prova do sinal.

Base de revisão: PR #85, agent/first-odd-green (ba5b0a3). A PR #41 continua independente e intacta. Fonte, métrica, amplitudes, fases, bordos, completion, pins e módulos históricos não foram alterados. Sem merge automático.

Validação: 15 comandos com saída zero, incluindo builds focados e raiz com --wfail, auditorias Foundation/Geometry/Analysis e inspeção de tipos/corpos de 52 raízes públicas (38 teoremas e 14 definições), com 6.343 dependências. Somente propext, Classical.choice e Quot.sound. Diagnóstico a 80/120 dígitos, sem entradas de zeros/alturas. Reprodução e hashes: REPORT.md, Audit.lean e evidence/validation.json.
