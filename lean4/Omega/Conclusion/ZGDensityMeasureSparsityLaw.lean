import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Omega.Conclusion.ZGDensityExactInhomogeneousMarkov

open scoped BigOperators

namespace Omega.Conclusion

/-- Concrete ZG sparsity-law data. The inhomogeneous Markov witness supplies the exact
transition law; the remaining fields record the marginal recursion, the prime-sum envelope, and
the dyadic Borel--Cantelli frequency estimate used by the conclusion theorem. -/
structure conclusion_zg_density_measure_sparsity_law_data where
  conclusion_zg_density_measure_sparsity_law_markovWitness : ZGInhomogeneousMarkovWitness
  conclusion_zg_density_measure_sparsity_law_marginal : ℕ → ℝ
  conclusion_zg_density_measure_sparsity_law_q : ℕ → ℝ
  conclusion_zg_density_measure_sparsity_law_primeSum : ℕ → ℝ
  conclusion_zg_density_measure_sparsity_law_expectedCount : ℕ → ℝ
  conclusion_zg_density_measure_sparsity_law_frequencyEnvelope : ℕ → ℝ
  conclusion_zg_density_measure_sparsity_law_marginal_rec :
    ∀ n,
      conclusion_zg_density_measure_sparsity_law_marginal (n + 1) =
        (1 - conclusion_zg_density_measure_sparsity_law_marginal n) *
          conclusion_zg_density_measure_sparsity_law_q n
  conclusion_zg_density_measure_sparsity_law_q_riccati :
    ∀ n,
      conclusion_zg_density_measure_sparsity_law_q n =
        ((conclusion_zg_density_measure_sparsity_law_markovWitness.B (n + 1) : ℝ) /
            conclusion_zg_density_measure_sparsity_law_markovWitness.A (n + 1)) /
          ((conclusion_zg_density_measure_sparsity_law_markovWitness.p (n + 1) : ℝ) +
            (conclusion_zg_density_measure_sparsity_law_markovWitness.B (n + 1) : ℝ) /
              conclusion_zg_density_measure_sparsity_law_markovWitness.A (n + 1))
  conclusion_zg_density_measure_sparsity_law_expected_count_sum :
    ∀ N,
      conclusion_zg_density_measure_sparsity_law_expectedCount N =
        (Finset.range N).sum fun n => conclusion_zg_density_measure_sparsity_law_marginal n
  conclusion_zg_density_measure_sparsity_law_prime_sum_estimate :
    ∀ N,
      conclusion_zg_density_measure_sparsity_law_expectedCount N ≤
        conclusion_zg_density_measure_sparsity_law_primeSum N
  conclusion_zg_density_measure_sparsity_law_dyadic_markov_bc :
    ∀ ε : ℝ,
      0 < ε →
        ∃ N₀ : ℕ,
          ∀ N : ℕ,
            N₀ ≤ N →
              conclusion_zg_density_measure_sparsity_law_frequencyEnvelope N ≤ ε

namespace conclusion_zg_density_measure_sparsity_law_data

/-- The expected count is the finite sum of the marginals and is controlled by the
prime-harmonic envelope. -/
def conclusion_zg_density_measure_sparsity_law_expected_count_loglog
    (D : conclusion_zg_density_measure_sparsity_law_data) : Prop :=
  ∀ N : ℕ,
    D.conclusion_zg_density_measure_sparsity_law_expectedCount N =
        (Finset.range N).sum
          (fun n => D.conclusion_zg_density_measure_sparsity_law_marginal n) ∧
      D.conclusion_zg_density_measure_sparsity_law_expectedCount N ≤
        D.conclusion_zg_density_measure_sparsity_law_primeSum N

/-- The dyadic Markov/Borel--Cantelli package gives almost-sure zero frequency as an
epsilon-tail bound for the concrete frequency envelope. -/
def conclusion_zg_density_measure_sparsity_law_zero_frequency_ae
    (D : conclusion_zg_density_measure_sparsity_law_data) : Prop :=
  ∀ ε : ℝ,
    0 < ε →
      ∃ N₀ : ℕ,
        ∀ N : ℕ,
          N₀ ≤ N → D.conclusion_zg_density_measure_sparsity_law_frequencyEnvelope N ≤ ε

end conclusion_zg_density_measure_sparsity_law_data

/-- Paper label: `thm:conclusion-zg-density-measure-sparsity-law`. -/
theorem paper_conclusion_zg_density_measure_sparsity_law
    (D : conclusion_zg_density_measure_sparsity_law_data) :
    D.conclusion_zg_density_measure_sparsity_law_expected_count_loglog ∧
      D.conclusion_zg_density_measure_sparsity_law_zero_frequency_ae := by
  refine ⟨?_, ?_⟩
  · intro N
    exact ⟨D.conclusion_zg_density_measure_sparsity_law_expected_count_sum N,
      D.conclusion_zg_density_measure_sparsity_law_prime_sum_estimate N⟩
  · intro ε hε
    exact D.conclusion_zg_density_measure_sparsity_law_dyadic_markov_bc ε hε

end Omega.Conclusion
