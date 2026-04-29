import Mathlib.Tactic

namespace Omega.POM

/-- Concrete data for the exponential invariant used to recover the second collision radius after
a fixed positive renormalization prefactor. -/
structure pom_infonce_exponential_invariant_r2_identifiability_data where
  prefactor : ℝ
  r2 : ℝ
  renormalizedMoment : ℕ → ℝ
  prefactor_pos : 0 < prefactor

namespace pom_infonce_exponential_invariant_r2_identifiability_data

/-- The preceding second-order renormalization supplies the prefixed exponential moment exactly. -/
def second_order_renormalization
    (D : pom_infonce_exponential_invariant_r2_identifiability_data) : Prop :=
  ∀ m : ℕ, D.renormalizedMoment m = D.prefactor * D.r2 ^ m

/-- Dividing by the fixed positive prefactor leaves the exponential scale unchanged. -/
def exponential_limit
    (D : pom_infonce_exponential_invariant_r2_identifiability_data) : Prop :=
  ∀ m : ℕ, D.renormalizedMoment m / D.prefactor = D.r2 ^ m

/-- The displayed recovery formula rearranges the prefixed exponential data back to `r2 ^ m`. -/
def r2_recovery_formula
    (D : pom_infonce_exponential_invariant_r2_identifiability_data) : Prop :=
  ∀ m : ℕ, D.r2 ^ m = D.renormalizedMoment m / D.prefactor

end pom_infonce_exponential_invariant_r2_identifiability_data

/-- Paper label: `cor:pom-infonce-exponential-invariant-r2-identifiability`. -/
theorem paper_pom_infonce_exponential_invariant_r2_identifiability
    (D : pom_infonce_exponential_invariant_r2_identifiability_data) :
    D.second_order_renormalization -> D.exponential_limit ∧ D.r2_recovery_formula := by
  intro hrenorm
  have hpref_ne : D.prefactor ≠ 0 := ne_of_gt D.prefactor_pos
  refine ⟨?_, ?_⟩
  · intro m
    rw [hrenorm m]
    field_simp [hpref_ne]
  · intro m
    rw [hrenorm m]
    field_simp [hpref_ne]

end Omega.POM
