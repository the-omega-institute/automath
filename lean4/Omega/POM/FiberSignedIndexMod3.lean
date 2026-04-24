import Mathlib.Tactic
import Omega.Folding.FibonacciPolynomial

namespace Omega.POM

/-- Paper label: `cor:pom-fiber-signed-index-mod3`. -/
theorem paper_pom_fiber_signed_index_mod3 (L : List ℕ) :
    (((L.map pathIndSetPolyNegOne).prod = 0) ↔ ∃ ℓ ∈ L, ℓ % 3 = 1) := by
  rw [List.prod_eq_zero_iff]
  constructor
  · intro h
    rcases List.mem_map.1 h with ⟨ℓ, hℓ, hzero⟩
    exact ⟨ℓ, hℓ, (pathIndSetPolyNegOne_eq_zero_iff ℓ).mp hzero⟩
  · rintro ⟨ℓ, hℓ, hmod⟩
    exact List.mem_map.2 ⟨ℓ, hℓ, (pathIndSetPolyNegOne_eq_zero_iff ℓ).2 hmod⟩

end Omega.POM
