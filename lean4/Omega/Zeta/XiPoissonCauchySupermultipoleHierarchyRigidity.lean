import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete moment data for the supermultipole hierarchy. -/
structure xi_poisson_cauchy_supermultipole_hierarchy_rigidity_data where
  xi_poisson_cauchy_supermultipole_hierarchy_rigidity_mu : ℕ → ℤ

namespace xi_poisson_cauchy_supermultipole_hierarchy_rigidity_data

/-- Fast decay through level `m` means that no nonzero multipole moment appears between
orders `2` and `m`. -/
def xi_poisson_cauchy_supermultipole_hierarchy_rigidity_fastDecay
    (D : xi_poisson_cauchy_supermultipole_hierarchy_rigidity_data) (m : ℕ) : Prop :=
  ¬ ∃ k, 2 ≤ k ∧ k ≤ m ∧
    D.xi_poisson_cauchy_supermultipole_hierarchy_rigidity_mu k ≠ 0

end xi_poisson_cauchy_supermultipole_hierarchy_rigidity_data

open xi_poisson_cauchy_supermultipole_hierarchy_rigidity_data

/-- Paper label: `thm:xi-poisson-cauchy-supermultipole-hierarchy-rigidity`. -/
theorem paper_xi_poisson_cauchy_supermultipole_hierarchy_rigidity
    (D : xi_poisson_cauchy_supermultipole_hierarchy_rigidity_data) (m : ℕ) (hm : 2 ≤ m) :
    D.xi_poisson_cauchy_supermultipole_hierarchy_rigidity_fastDecay m ↔
      ∀ k, 2 ≤ k → k ≤ m →
        D.xi_poisson_cauchy_supermultipole_hierarchy_rigidity_mu k = 0 := by
  have _hm : 2 ≤ m := hm
  constructor
  · intro hfast k hk hkm
    by_contra hne
    exact hfast ⟨k, hk, hkm, hne⟩
  · intro hzero hnonzero
    rcases hnonzero with ⟨k, hk, hkm, hne⟩
    exact hne (hzero k hk hkm)

end Omega.Zeta
