# Dependências reais da formalização

## Proveniência e toolchain

- GoN: snapshot `6c5c97b03925c398bf77a561d6e76b14563265e0` (#324),
  `lean-toolchain` `leanprover/lean4:v4.32.0`.
- Mathlib: revisão fixada `81a5d257c8e410db227a6665ed08f64fea08e997` no
  `lake-manifest.json` desse snapshot.
- Carry: checkout usado para os artefatos de módulos existentes em
  `8f15ec76e5a95eb0c61da3a114729363a1d6a477`. O checkout está sujo por trabalho
  paralelo, mas os arquivos Carry citados abaixo estão limpos no `git status`.

## Grafo de imports utilizado

| Módulo desta tarefa | Dependência real | Uso |
| --- | --- | --- |
| `ResidualPadé.lean` | `GeneralCofactorIdentity.lean` local no snapshot | Reutiliza `cofactorVector` e `border_mulVec_cofactor`; não refaz a identidade de cofatores. |
| `ResidualPadé.lean` | `Mathlib.Data.Real.Basic`, `Matrix.NonsingularInverse`, `PowerSeries.Trunc`, `PowerSeries.Derivative` | Reais, determinantes/inversa apenas no corolário invertível, séries formais, derivada e truncação. |
| `ResidualNative.lean` | `SourceNative.lean` e `SourceBezout.lean` locais no snapshot | Usa a recorrência nativa e as definições de série nativas existentes. Ambos foram compilados localmente para esta execução. |
| `ResidualNative.lean` | `CarrySelfAdjointOperator.NativeSourceAllOrderSchur` | Identifica o Schur nativo e adapta `nativeSourceSchurRemainder_eq`. SHA-256 do fonte: `d7abc44bc54da0227e4ac46076d10cc49a98c0e9ff31f28346ff8aa05b7d3e03`. |
| `SourceNative.lean` | `CarrySelfAdjointOperator.CompletedNativeChiralReturnArbitraryOrder`, `CompletedNativeLogCoefficientMajorant`, `CompletedNativeChiralEvenBoundaryStieltjesGate` (transitivamente via o módulo acima) | Proveniência dos coeficientes nativos e do lema de resto Schur já existente. |

Os fontes `SourceNative.lean`, `SourceBezout.lean` e `SourceSchur.lean` no
snapshot têm os mesmos SHA-256 que os fontes no worktree de compensação TFVD:

```text
SourceNative.lean  9d22c9b0c3e6ae66e4ab75b8c266a5ba8633ff8bd74a62f62b648da6f2880a21
SourceBezout.lean  f81d9bf0d25c98989f9e7751d798f1ec8cafefe721515f6ebaa5792eecc7f68b
SourceSchur.lean   89cd220ce232948f56a9fb6717ddda8fbb8622ea7561785c18cfd0be92c4ef5a
```

`SourceSchur.lean` não é importado por esta prova. A identidade algébrica
principal não importa módulos Carry, `NativeHankelPencilCofactor` da CSA #109,
Hardy ou resultados de positividade. A ligação nativa fica restrita ao
adaptador da recorrência e ao escalar Schur já existente.

## Compilação explícita

Os comandos abaixo foram executados no worktree exato. O cache de módulos
Mathlib/Carry é lido do ambiente Lean; os `.olean` dos fontes GoN reutilizados
foram escritos no `.cache` local do worktree.

```bash
carry_path=$(cd /home/thlinux/carry-self-adjoint-operator && lake env printenv LEAN_PATH)
cache_path=/home/thlinux/worktrees/pade-sem-divisao-20261112/research/c3-cofactor-chiral-certification/.cache
source_cache=/home/thlinux/worktrees/pade-sem-divisao-20261112/research/tfvd-bezout-schur-residual/.cache

LEAN_PATH="$source_cache:$carry_path" lean -DwarningAsError=true \
  --root=research/tfvd-bezout-schur-residual \
  -o "$source_cache/SourceBezout.olean" \
  research/tfvd-bezout-schur-residual/SourceBezout.lean
LEAN_PATH="$source_cache:$carry_path" lean -DwarningAsError=true \
  --root=research/tfvd-bezout-schur-residual \
  -o "$source_cache/SourceNative.olean" \
  research/tfvd-bezout-schur-residual/SourceNative.lean
LEAN_PATH="$cache_path:$carry_path" lean -DwarningAsError=true \
  --root=research/c3-cofactor-chiral-certification \
  -o "$cache_path/GeneralCofactorIdentity.olean" \
  research/c3-cofactor-chiral-certification/GeneralCofactorIdentity.lean
LEAN_PATH="$cache_path:$carry_path" lean -DwarningAsError=true \
  --root=research/c3-cofactor-chiral-certification \
  -o "$cache_path/ResidualPadé.olean" \
  research/c3-cofactor-chiral-certification/ResidualPadé.lean
LEAN_PATH="$cache_path:$source_cache:$carry_path" lean -DwarningAsError=true \
  --root=research/c3-cofactor-chiral-certification \
  -o "$cache_path/ResidualNative.olean" \
  research/c3-cofactor-chiral-certification/ResidualNative.lean
LEAN_PATH="$cache_path:$source_cache:$carry_path" lean -DwarningAsError=true \
  --root=research/c3-cofactor-chiral-certification \
  -o "$cache_path/ResidualAudit.olean" \
  research/c3-cofactor-chiral-certification/ResidualAudit.lean
```

O `#print axioms` imprime apenas `propext`, `Classical.choice` e `Quot.sound`
para os teoremas auditados; não aparecem `sorryAx`, axioma próprio ou escape
de confiança.
