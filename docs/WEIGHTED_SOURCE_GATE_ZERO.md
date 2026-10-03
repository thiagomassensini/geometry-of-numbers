# Gate zero — classificação anterior a qualquer definição nova

STATUS: SEMANTIC_DIAGONAL_GAP.

| Objeto | Papel literal do índice | Classificação | Evidência |
| --- | --- | --- | --- |
| realSpectralState t n | Amostra material do ponto positivo n+1 | DEFINITIONAL | Definição do estado e nativeLogGenerator_basisVector_log |
| q^n em nativeCarryWeightedRealSpectralState | Expoente do MESMO índice de armazenamento/amostragem n | DEFINITIONAL | nativeCarryWeightedRealSpectralState_apply := rfl |
| Interpretação desse expoente como positional depth de n+1 | Não há crosswalk demonstrado | DOCUMENTED-ONLY | Comentário vertical do módulo; sem theorem de identificação |
| CarryVerticalL2 coordinate | Coordenada da sequência vertical sobre a qual shifts/TFVD atuam | DEFINITIONAL | lp e fórmulas de shift/bracket/trace; gauge R2 registra o eixo |
| positionalDepth b N | Máximo expoente com b^k dividindo N no domínio b>1,N>0 | DERIVED | positionalDepth_spec |
| C2 fiber depth k | Parâmetro de 2^k m + epsilon; torna-se profundidade intrínseca do CENTRO sob core ímpar | DERIVED | c2AlignedCenter_padicDepth_eq_fiberDepth e c2AlignedIndex_factorization |
| C2 core m | Core ímpar canônico do centro; não o sample index | DERIVED | c2AlignedIndex_factorization/odd/pos; positionalDepth_factorization_existsUnique |
| materialLogPhase outer index | Label material Fin N; clock log(n.val+1), independente de k | DEFINITIONAL | MaterialLogTfvdCanary; encoder da source não fornecido |

NO_THEOREM_IDENTIFIES_MATERIAL_INDEX_WITH_POSITIONAL_DEPTH

Resultado da busca nos snapshots consultados: nenhum theorem liga o expoente
n do weighted state ao positionalDepth de sua quantidade material n+1.
A representação diagonal abstrata fica DIAGONAL_ONLY_REPRESENTATION.
Não foi construído X(n,k), encoder ou source bidimensional para forçar igualdade.
