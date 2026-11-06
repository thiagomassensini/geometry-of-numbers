# Registro do build C5 O3

O build foi executado em saída limpa com Lean 4.32.0 e `warningAsError=true`.
Os comandos, dependências e pins estão em `VALIDATION.md`. Os seis módulos
compilaram em ordem de dependência e cada processo terminou com status 0.

Módulos e logs individuais:

1. `SigmaFiniteRationalIntervals`
2. `SigmaFiniteRationalIntervalBoxes`
3. `SigmaFiniteRationalIntervalTransport`
4. `SigmaFiniteRationalIntervalSigns`
5. `SigmaFiniteRationalIntervalCertificates`
6. `SigmaFiniteRationalIntervalAudit`

`build-summary.log` registra que todos os seis `.olean` existem. Como Lean não
emite saída em uma compilação bem-sucedida sem warnings, cada log individual
pode estar vazio. Os hashes de fontes e `.olean` vinculam o resultado compilado
à revisão registrada neste checkpoint.

`axiom-audit.log` é a saída `#print axioms` do módulo de auditoria.
`axiom-audit-check.log` foi produzido por
`check_c5_rational_axioms.py` e confirma as 13 raízes obrigatórias, sem axiomas
além de `propext`, `Classical.choice` e `Quot.sound`.
