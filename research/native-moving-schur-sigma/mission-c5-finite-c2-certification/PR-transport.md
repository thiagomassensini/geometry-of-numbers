## Escopo

Esta PR integra a Fase 1 da missão C5: o transporte polinomial finito derivado da fonte C4 original. C0–C4 não foram refeitos.

## Prova

- `completedSigmaFiniteScaledMoment_recurrence` deriva a recorrência sem divisões de `p_n = c_0^(n+1) * (2 * completedSigmaLogJet d n)` da identidade C4 já integrada.
- `completedSigmaFiniteScaledMoment_minor_identity` prova `p_s*p_(s+2)-p_(s+1)^2 = 4*c_0^(2*s+4)*CarrySigmaPade.sigmaPadeD d s`.
- Os lemas de sinal usam `c_0 > 0` da fonte C4 e concluem sobre o `sigmaPadeD` original.
- Não redefine os jets nem presume sinais adicionais.

## Validação

- Lean 4.32: build limpo passou com warnings como erros.
- Auditoria `#print axioms` dos quatro teoremas: apenas `propext`, `Classical.choice` e `Quot.sound`.
- As verificações racionais e as três gerações intervalares existentes foram reproduzidas; esses sinais permanecem condicionais às caixas. Os logs, hashes e a falha/patch de compatibilidade do `gmpy2` estão versionados na pasta de evidências C5.

## Limite declarado

Esta PR **não** prova que os coeficientes da fonte C2 original pertencem às caixas e **não** declara os dois teoremas de primeira janela negativa. A certificação incondicional continua aberta para as próximas fases. A PR #2 do repositório Momentos permanece intacta e aberta.
