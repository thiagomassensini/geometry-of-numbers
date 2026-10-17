import CachedSourceProgram
namespace CarryIntegralCertificate
set_option autoImplicit false

/-- Interval for the actual scalar Taylor coefficient, before any moment readout. -/
def quadratureCoefficientComputation (m j r : ℕ) : Box :=
  (((polynomialBox r (cachedArgumentNode m j)).mul (cachedModeNode m j)).div
    (.point (r.factorial:ℤ)))

/-- Scalar majorant divided by 15!, before multiplication by its exact weight. -/
def quadratureErrorComputation (m j : ℕ) : Box :=
  (((cachedMajorantBox m 16 (j+1)).mul (cachedModeNode m j)).div
    (.point (Nat.factorial 15:ℤ)))

end CarryIntegralCertificate
