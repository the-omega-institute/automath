import Mathlib
import Omega.POM.MultiplicityCompositionPartCountGeneralqLLT

namespace Omega.POM

noncomputable section

/-- Low-temperature block weight for a composition part of energy `k`. -/
def pom_multiplicity_low_temperature_gibbs_block_weight (β : ℝ) (k : ℕ) : ℝ :=
  Real.exp (-(β * (k : ℝ)))

/-- Gibbs weight of a finite ordered composition prefix. -/
def pom_multiplicity_low_temperature_gibbs_composition_weight
    (β : ℝ) (parts : List ℕ) : ℝ :=
  (parts.map fun k => pom_multiplicity_low_temperature_gibbs_block_weight β k).prod

/-- The two-term low-temperature partition wrapper: ground state plus first excitation. -/
def pom_multiplicity_low_temperature_gibbs_two_term_partition (β : ℝ) : ℝ :=
  pom_multiplicity_low_temperature_gibbs_block_weight β 0 +
    pom_multiplicity_low_temperature_gibbs_block_weight β 1

/-- One-step Gibbs law induced by the two-term partition wrapper. -/
def pom_multiplicity_low_temperature_gibbs_one_step_law (β : ℝ) (k : ℕ) : ℝ :=
  pom_multiplicity_low_temperature_gibbs_block_weight β k /
    pom_multiplicity_low_temperature_gibbs_two_term_partition β

/-- Product law assigned to a fixed finite prefix. -/
def pom_multiplicity_low_temperature_gibbs_prefix_iid_law
    (β : ℝ) (parts : List ℕ) : ℝ :=
  (parts.map fun k => pom_multiplicity_low_temperature_gibbs_one_step_law β k).prod

/-- Concrete package for the q-tilted composition Gibbs model. It records the already-audited
partition-function wrapper, the finite prefix/tail factorization, the induced i.i.d. prefix law,
and the low-temperature two-term partition and first-excitation probability. -/
def pom_multiplicity_low_temperature_gibbs_statement : Prop :=
  pomMultiplicityCompositionPartcountGeneralqLLTClaim ∧
    (∀ β : ℝ, ∀ head tail : List ℕ,
      pom_multiplicity_low_temperature_gibbs_composition_weight β (head ++ tail) =
        pom_multiplicity_low_temperature_gibbs_composition_weight β head *
          pom_multiplicity_low_temperature_gibbs_composition_weight β tail) ∧
    (∀ β : ℝ, ∀ parts : List ℕ,
      pom_multiplicity_low_temperature_gibbs_prefix_iid_law β parts =
        (parts.map fun k => pom_multiplicity_low_temperature_gibbs_one_step_law β k).prod) ∧
    (∀ β : ℝ,
      pom_multiplicity_low_temperature_gibbs_two_term_partition β =
        1 + Real.exp (-β)) ∧
    (∀ β : ℝ,
      pom_multiplicity_low_temperature_gibbs_one_step_law β 1 =
        Real.exp (-β) / (1 + Real.exp (-β)))

/-- Paper label: `prop:pom-multiplicity-low-temperature-gibbs`. -/
theorem paper_pom_multiplicity_low_temperature_gibbs :
    pom_multiplicity_low_temperature_gibbs_statement := by
  refine ⟨paper_pom_multiplicity_composition_partcount_generalq_llt, ?_, ?_, ?_, ?_⟩
  · intro β head tail
    simp [pom_multiplicity_low_temperature_gibbs_composition_weight, List.map_append,
      List.prod_append]
  · intro β parts
    rfl
  · intro β
    simp [pom_multiplicity_low_temperature_gibbs_two_term_partition,
      pom_multiplicity_low_temperature_gibbs_block_weight]
  · intro β
    simp [pom_multiplicity_low_temperature_gibbs_one_step_law,
      pom_multiplicity_low_temperature_gibbs_two_term_partition,
      pom_multiplicity_low_temperature_gibbs_block_weight]

end

end Omega.POM
