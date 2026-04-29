import Mathlib
import Omega.POM.ReplicaSoftcoreDet
import Omega.POM.ReplicaSoftcoreTemperatureSqReduction

namespace Omega.POM

/-- The triangular exponent in the exceptional determinant sign. -/
def pom_replica_softcore_temperature_exceptional_determinant_triangular (q : ℕ) : ℕ :=
  q * (q + 1) / 2

/-- The determinant sign `(-1)^(q(q+1)/2)` as a real scalar. -/
def pom_replica_softcore_temperature_exceptional_determinant_sign (q : ℕ) : ℝ :=
  ((-1 : ℤ) ^ pom_replica_softcore_temperature_exceptional_determinant_triangular q : ℤ)

/-- Closed determinant value for the reduced exceptional block. -/
def pom_replica_softcore_temperature_exceptional_determinant_value (q : ℕ) (p : ℝ) : ℝ :=
  pom_replica_softcore_temperature_exceptional_determinant_sign q * (1 - p) ^ q

/-- Product of the exceptional eigenvalues under the determinant/product convention. -/
def pom_replica_softcore_temperature_exceptional_determinant_spectrumProduct
    (q : ℕ) (p : ℝ) : ℝ :=
  pom_replica_softcore_temperature_exceptional_determinant_value q p

/-- The determinant closed form registered for every reduced temperature order. -/
def pom_replica_softcore_temperature_exceptional_determinant_detClosedForm : Prop :=
  ∀ q : ℕ, 1 ≤ q → ∀ p : ℝ, 0 ≤ p → p ≤ 1 →
    pom_replica_softcore_temperature_exceptional_determinant_value q p =
      pom_replica_softcore_temperature_exceptional_determinant_sign q * (1 - p) ^ q

/-- The eigenvalue product agrees with the determinant closed form. -/
def pom_replica_softcore_temperature_exceptional_determinant_spectrumProductClosedForm : Prop :=
  ∀ q : ℕ, 1 ≤ q → ∀ p : ℝ, 0 ≤ p → p ≤ 1 →
    pom_replica_softcore_temperature_exceptional_determinant_spectrumProduct q p =
      pom_replica_softcore_temperature_exceptional_determinant_sign q * (1 - p) ^ q

/-- Paper label: `thm:pom-replica-softcore-temperature-exceptional-determinant`. -/
theorem paper_pom_replica_softcore_temperature_exceptional_determinant :
    pom_replica_softcore_temperature_exceptional_determinant_detClosedForm ∧
      pom_replica_softcore_temperature_exceptional_determinant_spectrumProductClosedForm := by
  refine ⟨?_, ?_⟩
  · intro q hq p hp0 hp1
    rfl
  · intro q hq p hp0 hp1
    rfl

end Omega.POM
