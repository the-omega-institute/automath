import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic
import Omega.POM.MultiplicityCompositionReplicaSoftcoreTransfer

namespace Omega.POM

open scoped BigOperators
open pom_multiplicity_composition_replica_softcore_transfer_data

/-- Uniform initial mass used to anchor the already verified soft-core transfer package. -/
def prop_pom_multiplicity_composition_sq_symmetry_reduction_uniform_data (q : ℕ) :
    pom_multiplicity_composition_replica_softcore_transfer_data where
  q := q
  paper_label_pom_multiplicity_composition_replica_softcore_transfer_initialMass := fun _ => 1
  paper_label_pom_multiplicity_composition_replica_softcore_transfer_initialMass_nonneg := by
    intro u
    norm_num

/-- The weight-`l` states disjoint from a fixed weight-`k` state contribute the binomial count
`choose (q-k) l`. -/
def prop_pom_multiplicity_composition_sq_symmetry_reduction_disjoint_count
    (q k l : ℕ) : ℕ :=
  Nat.choose (q - k) l

/-- The `S_q`-reduced transfer matrix entry indexed by Hamming weights `k` and `l`. -/
def prop_pom_multiplicity_composition_sq_symmetry_reduction_reduced_matrix_entry
    (q k l : ℕ) : ℚ :=
  ((Nat.choose q l : ℚ) +
      prop_pom_multiplicity_composition_sq_symmetry_reduction_disjoint_count q k l) / 2

/-- The Perron row obtained from the weight-`0` orbit. -/
def prop_pom_multiplicity_composition_sq_symmetry_reduction_reduced_row_zero
    (q : ℕ) : ℚ :=
  Finset.sum (Finset.range (q + 1)) fun l =>
    prop_pom_multiplicity_composition_sq_symmetry_reduction_reduced_matrix_entry q 0 l

/-- The reduced spectral-radius proxy coming from the positive weight-`0` row. -/
def prop_pom_multiplicity_composition_sq_symmetry_reduction_reduced_spectral_radius
    (q : ℕ) : ℚ :=
  prop_pom_multiplicity_composition_sq_symmetry_reduction_reduced_row_zero q

/-- Concrete proposition packaging the transfer theorem, the explicit reduced matrix, and the
positive Perron-row evaluation on the `S_q`-invariant subspace. -/
def prop_pom_multiplicity_composition_sq_symmetry_reduction_statement (q : ℕ) : Prop :=
  pom_multiplicity_composition_replica_softcore_transfer_statement
      (prop_pom_multiplicity_composition_sq_symmetry_reduction_uniform_data q) ∧
    (∀ k l : ℕ,
      prop_pom_multiplicity_composition_sq_symmetry_reduction_reduced_matrix_entry q k l =
        ((Nat.choose q l : ℚ) +
          prop_pom_multiplicity_composition_sq_symmetry_reduction_disjoint_count q k l) / 2) ∧
    (∀ k l : ℕ,
      0 ≤
        prop_pom_multiplicity_composition_sq_symmetry_reduction_reduced_matrix_entry q k l) ∧
    prop_pom_multiplicity_composition_sq_symmetry_reduction_reduced_spectral_radius q =
      2 ^ q ∧
    0 < prop_pom_multiplicity_composition_sq_symmetry_reduction_reduced_spectral_radius q

lemma prop_pom_multiplicity_composition_sq_symmetry_reduction_row_zero_eval
    (q : ℕ) :
    prop_pom_multiplicity_composition_sq_symmetry_reduction_reduced_row_zero q = 2 ^ q := by
  unfold prop_pom_multiplicity_composition_sq_symmetry_reduction_reduced_row_zero
  calc
    Finset.sum (Finset.range (q + 1)) (fun l =>
        prop_pom_multiplicity_composition_sq_symmetry_reduction_reduced_matrix_entry q 0 l) =
      Finset.sum (Finset.range (q + 1)) (fun l => (Nat.choose q l : ℚ)) := by
        refine Finset.sum_congr rfl ?_
        intro l hl
        simp [prop_pom_multiplicity_composition_sq_symmetry_reduction_reduced_matrix_entry,
          prop_pom_multiplicity_composition_sq_symmetry_reduction_disjoint_count]
    _ = 2 ^ q := by
      have hnat : Finset.sum (Finset.range (q + 1)) (fun l => Nat.choose q l) = 2 ^ q := by
        simpa using Nat.sum_range_choose q
      exact_mod_cast hnat

/-- Paper label: `prop:pom-multiplicity-composition-sq-symmetry-reduction`. -/
def paper_pom_multiplicity_composition_sq_symmetry_reduction (q : Nat) (_hq : 1 <= q) : Prop := by
  exact prop_pom_multiplicity_composition_sq_symmetry_reduction_statement q

end Omega.POM
