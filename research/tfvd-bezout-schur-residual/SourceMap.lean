module
public import SourceBezout

@[expose] public section
namespace CarrySourceBezout
noncomputable section
variable {R S : Type*} [CommRing R] [CommRing S]

def mapBi (φ : R →+* S) : BiSeries R →+* BiSeries S :=
  PowerSeries.map (PowerSeries.map φ)

theorem sourceSeries_map (φ : R →+* S) (c : ℕ → R) :
    sourceSeries (fun n => φ (c n)) = PowerSeries.map φ (sourceSeries c) := by
  apply PowerSeries.ext
  intro n
  simp [sourceSeries]

theorem divided_map (φ : R →+* S) (a : PowerSeries R) :
    divided (PowerSeries.map φ a) = mapBi φ (divided a) := by
  apply PowerSeries.ext
  intro i
  apply PowerSeries.ext
  intro j
  simp [divided, mapBi]

theorem right_map (φ : R →+* S) (a : PowerSeries R) :
    right (PowerSeries.map φ a) = mapBi φ (right a) := by
  apply PowerSeries.ext
  intro i
  apply PowerSeries.ext
  intro j
  by_cases hi : i = 0 <;> simp [right, mapBi, PowerSeries.coeff_C, hi]

theorem bezout_map (φ : R →+* S) (a c : PowerSeries R) :
    bezout (PowerSeries.map φ a) (PowerSeries.map φ c) = mapBi φ (bezout a c) := by
  simp only [bezout, divided_map, right_map, map_sub, map_mul]

theorem derivative_map (φ : R →+* S) (a : PowerSeries R) :
    PowerSeries.derivative S (PowerSeries.map φ a) =
      PowerSeries.map φ (PowerSeries.derivative R a) := by
  apply PowerSeries.ext
  intro n
  simp [PowerSeries.coeff_derivative]

theorem sourceKernel_map (φ : R →+* S) (c : ℕ → R) (b : Bool) :
    sourceKernel (fun n => φ (c n)) b = mapBi φ (sourceKernel c b) := by
  cases b
  · change bezout (PowerSeries.X * -(PowerSeries.derivative S
      (sourceSeries (fun n => φ (c n))))) (sourceSeries (fun n => φ (c n))) = _
    rw [sourceSeries_map, derivative_map, ← map_neg, ← PowerSeries.map_X φ,
      ← map_mul, bezout_map]
    rfl
  · change bezout (-(PowerSeries.derivative S
      (sourceSeries (fun n => φ (c n))))) (sourceSeries (fun n => φ (c n))) = _
    rw [sourceSeries_map, derivative_map, ← map_neg, bezout_map]
    rfl

theorem coefficientBlock_map (φ : R →+* S) (f : BiSeries R) (n : ℕ) :
    coefficientBlock (mapBi φ f) n = (coefficientBlock f n).map φ := by
  ext i j
  simp [coefficientBlock, mapBi]

end
end CarrySourceBezout
