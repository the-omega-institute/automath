import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- The number of path components in the toggle decomposition. -/
structure pom_toggle_gauge_invariant_endomorphisms_c2_tensor_data where
  r : ℕ

/-- The single-component commutant has the two basis vectors corresponding to `I` and `J`. -/
abbrev pom_toggle_gauge_invariant_endomorphisms_c2_tensor_component_basis := Bool

/-- Tensoring the two-dimensional single-component basis across `r` components. -/
abbrev pom_toggle_gauge_invariant_endomorphisms_c2_tensor_tensor_basis
    (x : pom_toggle_gauge_invariant_endomorphisms_c2_tensor_data) :=
  Fin x.r → pom_toggle_gauge_invariant_endomorphisms_c2_tensor_component_basis

/-- Choosing `I` or `J` in each component is equivalent to choosing a subset of components. -/
def pom_toggle_gauge_invariant_endomorphisms_c2_tensor_sector_equiv
    (x : pom_toggle_gauge_invariant_endomorphisms_c2_tensor_data) :
    pom_toggle_gauge_invariant_endomorphisms_c2_tensor_tensor_basis x ≃ Finset (Fin x.r) where
  toFun f := Finset.univ.filter fun i => f i
  invFun S i := decide (i ∈ S)
  left_inv f := by
    funext i
    by_cases hi : f i
    · simp [hi]
    · simp [hi]
  right_inv S := by
    ext i
    simp

/-- Paper-facing statement: the single-component commutant is two-dimensional, the tensor product
has dimension `2^r`, and its natural basis is indexed by subsets of the `r` components. -/
def pom_toggle_gauge_invariant_endomorphisms_c2_tensor_statement
    (x : pom_toggle_gauge_invariant_endomorphisms_c2_tensor_data) : Prop :=
  Fintype.card pom_toggle_gauge_invariant_endomorphisms_c2_tensor_component_basis = 2 ∧
    Fintype.card (pom_toggle_gauge_invariant_endomorphisms_c2_tensor_tensor_basis x) = 2 ^ x.r ∧
    Nonempty
      (pom_toggle_gauge_invariant_endomorphisms_c2_tensor_tensor_basis x ≃ Finset (Fin x.r))

/-- Paper label: `thm:pom-toggle-gauge-invariant-endomorphisms-c2-tensor`. -/
theorem paper_pom_toggle_gauge_invariant_endomorphisms_c2_tensor
    (x : pom_toggle_gauge_invariant_endomorphisms_c2_tensor_data) :
    pom_toggle_gauge_invariant_endomorphisms_c2_tensor_statement x := by
  refine ⟨by decide, ?_, ⟨pom_toggle_gauge_invariant_endomorphisms_c2_tensor_sector_equiv x⟩⟩
  simpa [pom_toggle_gauge_invariant_endomorphisms_c2_tensor_tensor_basis,
    pom_toggle_gauge_invariant_endomorphisms_c2_tensor_component_basis] using
    (Fintype.card_fun (Fin x.r) Bool)

end Omega.POM
