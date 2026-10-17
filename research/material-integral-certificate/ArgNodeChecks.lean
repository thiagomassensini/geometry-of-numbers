import NodeCacheData
namespace CarryIntegralCertificate
set_option maxRecDepth 65536
set_option maxHeartbeats 48000000

theorem argument_node_checks : ∀ m : Fin 3, ∀ j : Fin (thetaCertificateCellCount m.val+1),
    argumentBox m.val (gridBox j.val 64) = cachedArgumentNode m.val j.val := by
  decide +kernel

end CarryIntegralCertificate
