# Fonte dos lemas reutilizados

Os quatro arquivos de `MomentosHankel/` foram copiados de `thiagomassensini/momentos`, commit `05c9314d59306383baa55ed3be80ab950e799e97`, pasta `lean/MomentosHankel/`.

- `SchurPivotCurvature.lean`: vetor de Schur, relação de blocos e transporte euclidiano.
- `PivotSecondDerivative.lean`: identidade variacional genérica.
- `SchurVectorSmoothness.lean`: diferenciabilidade do inverso e do vetor crítico.
- `PivotLocalTransport.lean`: versão numa vizinhança aberta do centro.

Todas as declarações e provas foram preservadas; foi removida somente uma linha vazia excedente no fim de `SchurPivotCurvature.lean`. `evidence/vendor-manifest.json` registra seus hashes e a igualdade com a fonte. São recompilados por `validate.sh` usando o Mathlib já fixado nesta branch; nenhum pin ou dependência foi modificado. A instanciação na característica canônica fica nos módulos próprios desta investigação.
