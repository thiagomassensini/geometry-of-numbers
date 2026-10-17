import NodeCacheData
namespace CarryIntegralCertificate
set_option maxRecDepth 65536
set_option maxHeartbeats 48000000

theorem mode_node_checks : ∀ m : Fin 3, ∀ j : Fin (thetaCertificateCellCount m.val+1),
    modeNodeComputation m.val j.val = cachedModeNode m.val j.val := by
  decide +kernel

end CarryIntegralCertificate
