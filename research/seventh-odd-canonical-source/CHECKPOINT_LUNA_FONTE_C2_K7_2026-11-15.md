# Luna Fonte C2 — checkpoint K7

Data: 15/11/2026
Base: `geometry-of-numbers` main, `ca621765d4a4c1c1254a7df282d95926f29d362f`
Branch: `codex/luna-fonte-c2-k7-source-20261115`

## Resultado compilado: certificado racional condicional

`C2K7RationalConditional.lean` porta para Lean as 14 caixas inteiras de
`certificado_racional_H7_K7_48casas.json`. Cada caixa é armazenada como
`Box.finite` na escala interna `10^60`; os numeradores do arquivo, cujo
denominador é `10^48`, foram multiplicados exatamente por `10^12`.

Foi formalizado:

```lean
(∀ q : Fin 14, (c2K7MomentBoxes q).Mem (CarryCriticalSource.h q.val)) →
  (sourceMomentMatrix h 1 7).PosDef
```

e, pela ponte existente `k7_matrix_posDef_iff_pivot`, também

```lean
(∀ q : Fin 14, (c2K7MomentBoxes q).Mem (h q.val)) →
  0 < sourceMomentSchur h 1 6
```

O certificado repete a LDL do verificador racional em `200^(i+j+1)h(i+j+1)`.
`decide +kernel` confirma que as sete caixas de pivô escalado são positivas.
A transferência para a matriz original usa o vetor `yᵢ=xᵢ/200^i` e a
identidade quadrática exata `q_scaled(y)=200 q_K7(x)`. Não se identifica o
pivô com o menor autovalor, e a prova preserva os cruzamentos da matriz
Hankel original.

Foram reutilizados `K7PivotBridge`, `OddTrialPositivity`, o tipo `Box` e
`carryPairingCholesky_posDef`. As dependências transitivas da auditoria
imprimem apenas `[propext, Classical.choice, Quot.sound]`. Os módulos
`C2K7RationalConditional.lean` e `C2K7RationalConditionalAudit.lean` compilam
com warnings como erros. Não há `sorry`, `admit` nem axioma novo.

## Limite exato da conclusão

As caixas são uma hipótese explícita do teorema condicional. Este trabalho
**não prova** que os momentos canônicos da fonte pertencem a elas; portanto,
não prova incondicionalmente a positividade K7.

O K7 existente reduz o sinal ao gate

```text
3024*T26 - T28 < 4*28! * sourceCeiling 1 6.
```

O GoN já contém uma caixa certificada para `T26` e o método theta genérico
produz uma caixa larga para `T28`, mas não encontrei uma enclosure correlacionada
e estreita do teto Schur odd `sourceCeiling 1 6` que descarregue esse gate. As
caixas históricas de momentos do K6 só cobrem até `h11` e não implicam as novas
caixas de 48 casas para `h0,…,h13`.

O único próximo lema de fonte necessário para ativar diretamente o resultado
condicional é

```lean
theorem c2K7_native_moments_mem_rational_boxes :
  ∀ q : Fin 14,
    (c2K7MomentBoxes q).Mem (CarryCriticalSource.h q.val)
```

Ele precisa ser provado a partir da carta C2 completa, do completamento e do
resto analítico da cauda. Os dois cortes numéricos do pacote dão enclosures
compatíveis, mas continuam sendo evidência computacional externa ao kernel.

## Validação reproduzível

```sh
cd /home/thlinux/worktrees/luna-fonte-c2-k7-source-20261115
research/seventh-odd-canonical-source/compile_module.sh C2K7RationalConditional
research/seventh-odd-canonical-source/compile_module.sh C2K7RationalConditionalAudit
```

O script compila com `-DwarningAsError=true`, usa o cache Lean já existente e
guarda os `.olean` novos somente no worktree isolado. Nenhuma alteração dos
checkouts originais, commit, push ou merge foi feita.
