import Omega.Zeta.XiExteriorPowerPoincareDuality
import Omega.Zeta.XiExteriorPowerSmithSchubert

namespace Omega.Zeta

open scoped BigOperators

/-- Paper label: `cor:xi-exterior-power-jordan-schubert`. -/
theorem paper_xi_exterior_power_jordan_schubert (q k : ℕ) (hq : 2 ≤ q) (hk1 : 1 ≤ k)
    (hkq : k ≤ q + 1) :
    (xiExteriorPowerSmithExponentMultiset q k).card = Nat.choose (q + 1) k ∧
      (∀ S, S ∈ (Finset.range (q + 1)).powersetCard k →
        Finset.sum S (fun i => i) ∈ xiExteriorPowerSmithExponentMultiset q k) ∧
      (∀ S, S ∈ (Finset.range (q + 1)).powersetCard k →
        ∃ T, T ∈ (Finset.range (q + 1)).powersetCard k ∧
          Finset.sum S (fun i => i) + Finset.sum T (fun i => i) = k * q) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (paper_xi_exterior_power_smith_schubert q k hq hk1 hkq).1
  · intro S hS
    exact List.mem_map.2 ⟨S, by simpa using hS, rfl⟩
  · intro S hS
    exact paper_xi_exterior_power_poincare_duality q k hkq S hS

end Omega.Zeta
