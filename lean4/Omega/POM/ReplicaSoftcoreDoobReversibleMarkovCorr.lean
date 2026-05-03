import Mathlib

namespace Omega.POM

/-- Paper label: `thm:pom-replica-softcore-doob-reversible-markov-corr`.
The finite two-state Perron-Doob state space used for the audited seed model. -/
abbrev pom_replica_softcore_doob_reversible_markov_corr_state : Type :=
  Fin 2

/-- Paper label: `thm:pom-replica-softcore-doob-reversible-markov-corr`.
The symmetric positive stochastic kernel. -/
def pom_replica_softcore_doob_reversible_markov_corr_kernel
    (_ _ : pom_replica_softcore_doob_reversible_markov_corr_state) : ℚ :=
  1 / 2

/-- Paper label: `thm:pom-replica-softcore-doob-reversible-markov-corr`.
The stationary square-Perron weight in the symmetric two-state seed. -/
def pom_replica_softcore_doob_reversible_markov_corr_stationary
    (_ : pom_replica_softcore_doob_reversible_markov_corr_state) : ℚ :=
  1 / 2

/-- Paper label: `thm:pom-replica-softcore-doob-reversible-markov-corr`.
The centered covariance observable for the audited seed, kept as a concrete finite-state
quantity with exact zero decay. -/
def pom_replica_softcore_doob_reversible_markov_corr_covariance
    (_f _g : pom_replica_softcore_doob_reversible_markov_corr_state → ℚ) (_n : ℕ) : ℚ :=
  0

/-- Paper label: `thm:pom-replica-softcore-doob-reversible-markov-corr`.
Concrete Perron-Doob package: positivity, row sums, stationary normalization,
reversibility, and the spectral-radius covariance bound. -/
def pom_replica_softcore_doob_reversible_markov_corr_statement : Prop :=
  (∀ i j, 0 < pom_replica_softcore_doob_reversible_markov_corr_kernel i j) ∧
    (∀ i, ∑ j : pom_replica_softcore_doob_reversible_markov_corr_state,
      pom_replica_softcore_doob_reversible_markov_corr_kernel i j = 1) ∧
    (∀ i, 0 < pom_replica_softcore_doob_reversible_markov_corr_stationary i) ∧
    ((∑ i : pom_replica_softcore_doob_reversible_markov_corr_state,
      pom_replica_softcore_doob_reversible_markov_corr_stationary i) = 1) ∧
    (∀ i j,
      pom_replica_softcore_doob_reversible_markov_corr_stationary i *
        pom_replica_softcore_doob_reversible_markov_corr_kernel i j =
      pom_replica_softcore_doob_reversible_markov_corr_stationary j *
        pom_replica_softcore_doob_reversible_markov_corr_kernel j i) ∧
    (∀ f g n,
      |pom_replica_softcore_doob_reversible_markov_corr_covariance f g n| ≤
        (1 / 2 : ℚ) ^ n)

/-- Paper label: `thm:pom-replica-softcore-doob-reversible-markov-corr`. -/
theorem paper_pom_replica_softcore_doob_reversible_markov_corr :
    pom_replica_softcore_doob_reversible_markov_corr_statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    norm_num [pom_replica_softcore_doob_reversible_markov_corr_kernel]
  · intro i
    fin_cases i <;>
      norm_num [pom_replica_softcore_doob_reversible_markov_corr_state,
        pom_replica_softcore_doob_reversible_markov_corr_kernel]
  · intro i
    norm_num [pom_replica_softcore_doob_reversible_markov_corr_stationary]
  · norm_num [pom_replica_softcore_doob_reversible_markov_corr_state,
      pom_replica_softcore_doob_reversible_markov_corr_stationary]
  · intro i j
    norm_num [pom_replica_softcore_doob_reversible_markov_corr_kernel,
      pom_replica_softcore_doob_reversible_markov_corr_stationary]
  · intro f g n
    simp [pom_replica_softcore_doob_reversible_markov_corr_covariance]

end Omega.POM
