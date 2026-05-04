import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- A candidate finite square-spectrum package with `K` squared nodes, integral multiplicities,
odd weights, and a sampled scalar moment sequence. -/
structure conclusion_decoupled_square_spectrum_finite_sampling_candidate
    (conclusion_decoupled_square_spectrum_finite_sampling_K : ℕ) where
  conclusion_decoupled_square_spectrum_finite_sampling_candidate_node :
    Fin conclusion_decoupled_square_spectrum_finite_sampling_K → ℝ
  conclusion_decoupled_square_spectrum_finite_sampling_candidate_multiplicity :
    Fin conclusion_decoupled_square_spectrum_finite_sampling_K → ℕ
  conclusion_decoupled_square_spectrum_finite_sampling_candidate_oddWeight :
    Fin conclusion_decoupled_square_spectrum_finite_sampling_K → ℝ
  conclusion_decoupled_square_spectrum_finite_sampling_candidate_sample : ℕ → ℝ

/-- Even samples are the exponential sum with multiplicity plus odd weight. -/
noncomputable def conclusion_decoupled_square_spectrum_finite_sampling_even_sum
    {conclusion_decoupled_square_spectrum_finite_sampling_K : ℕ}
    (conclusion_decoupled_square_spectrum_finite_sampling_node :
      Fin conclusion_decoupled_square_spectrum_finite_sampling_K → ℝ)
    (conclusion_decoupled_square_spectrum_finite_sampling_multiplicity :
      Fin conclusion_decoupled_square_spectrum_finite_sampling_K → ℕ)
    (conclusion_decoupled_square_spectrum_finite_sampling_oddWeight :
      Fin conclusion_decoupled_square_spectrum_finite_sampling_K → ℝ)
    (conclusion_decoupled_square_spectrum_finite_sampling_n : ℕ) : ℝ :=
  ∑ j,
    ((conclusion_decoupled_square_spectrum_finite_sampling_multiplicity j : ℝ) +
        conclusion_decoupled_square_spectrum_finite_sampling_oddWeight j) *
      conclusion_decoupled_square_spectrum_finite_sampling_node j ^
        conclusion_decoupled_square_spectrum_finite_sampling_n

/-- Odd samples are the exponential sum with multiplicity minus odd weight. -/
noncomputable def conclusion_decoupled_square_spectrum_finite_sampling_odd_sum
    {conclusion_decoupled_square_spectrum_finite_sampling_K : ℕ}
    (conclusion_decoupled_square_spectrum_finite_sampling_node :
      Fin conclusion_decoupled_square_spectrum_finite_sampling_K → ℝ)
    (conclusion_decoupled_square_spectrum_finite_sampling_multiplicity :
      Fin conclusion_decoupled_square_spectrum_finite_sampling_K → ℕ)
    (conclusion_decoupled_square_spectrum_finite_sampling_oddWeight :
      Fin conclusion_decoupled_square_spectrum_finite_sampling_K → ℝ)
    (conclusion_decoupled_square_spectrum_finite_sampling_n : ℕ) : ℝ :=
  ∑ j,
    ((conclusion_decoupled_square_spectrum_finite_sampling_multiplicity j : ℝ) -
        conclusion_decoupled_square_spectrum_finite_sampling_oddWeight j) *
      conclusion_decoupled_square_spectrum_finite_sampling_node j ^
        conclusion_decoupled_square_spectrum_finite_sampling_n

/-- The candidate's even-indexed samples realize the even square-spectrum sum. -/
noncomputable def conclusion_decoupled_square_spectrum_finite_sampling_candidate_even_decomposition
    {conclusion_decoupled_square_spectrum_finite_sampling_K : ℕ}
    (E :
      conclusion_decoupled_square_spectrum_finite_sampling_candidate
        conclusion_decoupled_square_spectrum_finite_sampling_K) : Prop :=
  ∀ n,
    E.conclusion_decoupled_square_spectrum_finite_sampling_candidate_sample (2 * n) =
      conclusion_decoupled_square_spectrum_finite_sampling_even_sum
        E.conclusion_decoupled_square_spectrum_finite_sampling_candidate_node
        E.conclusion_decoupled_square_spectrum_finite_sampling_candidate_multiplicity
        E.conclusion_decoupled_square_spectrum_finite_sampling_candidate_oddWeight n

/-- The candidate's odd-indexed samples realize the odd square-spectrum sum. -/
noncomputable def conclusion_decoupled_square_spectrum_finite_sampling_candidate_odd_decomposition
    {conclusion_decoupled_square_spectrum_finite_sampling_K : ℕ}
    (E :
      conclusion_decoupled_square_spectrum_finite_sampling_candidate
        conclusion_decoupled_square_spectrum_finite_sampling_K) : Prop :=
  ∀ n,
    E.conclusion_decoupled_square_spectrum_finite_sampling_candidate_sample (2 * n + 1) =
      conclusion_decoupled_square_spectrum_finite_sampling_odd_sum
        E.conclusion_decoupled_square_spectrum_finite_sampling_candidate_node
        E.conclusion_decoupled_square_spectrum_finite_sampling_candidate_multiplicity
        E.conclusion_decoupled_square_spectrum_finite_sampling_candidate_oddWeight n

/-- Concrete data for the decoupled square-spectrum finite-sampling theorem. The final field is
the finite Vandermonde/Prony recovery certificate: any candidate with the same first `2*K`
samples and the same even/odd moment laws has the same nodes, multiplicities, and odd weights. -/
structure conclusion_decoupled_square_spectrum_finite_sampling_data where
  conclusion_decoupled_square_spectrum_finite_sampling_K : ℕ
  conclusion_decoupled_square_spectrum_finite_sampling_node :
    Fin conclusion_decoupled_square_spectrum_finite_sampling_K → ℝ
  conclusion_decoupled_square_spectrum_finite_sampling_multiplicity :
    Fin conclusion_decoupled_square_spectrum_finite_sampling_K → ℕ
  conclusion_decoupled_square_spectrum_finite_sampling_oddWeight :
    Fin conclusion_decoupled_square_spectrum_finite_sampling_K → ℝ
  conclusion_decoupled_square_spectrum_finite_sampling_sample : ℕ → ℝ
  conclusion_decoupled_square_spectrum_finite_sampling_distinct_squared_nodes :
    Function.Injective conclusion_decoupled_square_spectrum_finite_sampling_node
  conclusion_decoupled_square_spectrum_finite_sampling_even_moment_identity :
    ∀ n,
      conclusion_decoupled_square_spectrum_finite_sampling_sample (2 * n) =
        conclusion_decoupled_square_spectrum_finite_sampling_even_sum
          conclusion_decoupled_square_spectrum_finite_sampling_node
          conclusion_decoupled_square_spectrum_finite_sampling_multiplicity
          conclusion_decoupled_square_spectrum_finite_sampling_oddWeight n
  conclusion_decoupled_square_spectrum_finite_sampling_odd_moment_identity :
    ∀ n,
      conclusion_decoupled_square_spectrum_finite_sampling_sample (2 * n + 1) =
        conclusion_decoupled_square_spectrum_finite_sampling_odd_sum
          conclusion_decoupled_square_spectrum_finite_sampling_node
          conclusion_decoupled_square_spectrum_finite_sampling_multiplicity
          conclusion_decoupled_square_spectrum_finite_sampling_oddWeight n
  conclusion_decoupled_square_spectrum_finite_sampling_prony_recovery :
    ∀ E :
      conclusion_decoupled_square_spectrum_finite_sampling_candidate
        conclusion_decoupled_square_spectrum_finite_sampling_K,
      (∀ n,
        n < 2 * conclusion_decoupled_square_spectrum_finite_sampling_K →
          E.conclusion_decoupled_square_spectrum_finite_sampling_candidate_sample n =
            conclusion_decoupled_square_spectrum_finite_sampling_sample n) →
      conclusion_decoupled_square_spectrum_finite_sampling_candidate_even_decomposition E →
      conclusion_decoupled_square_spectrum_finite_sampling_candidate_odd_decomposition E →
        E.conclusion_decoupled_square_spectrum_finite_sampling_candidate_node =
            conclusion_decoupled_square_spectrum_finite_sampling_node ∧
          E.conclusion_decoupled_square_spectrum_finite_sampling_candidate_multiplicity =
            conclusion_decoupled_square_spectrum_finite_sampling_multiplicity ∧
            E.conclusion_decoupled_square_spectrum_finite_sampling_candidate_oddWeight =
              conclusion_decoupled_square_spectrum_finite_sampling_oddWeight

/-- The data package itself as a candidate spectrum. -/
noncomputable def conclusion_decoupled_square_spectrum_finite_sampling_data_candidate
    (D : conclusion_decoupled_square_spectrum_finite_sampling_data) :
    conclusion_decoupled_square_spectrum_finite_sampling_candidate
      D.conclusion_decoupled_square_spectrum_finite_sampling_K where
  conclusion_decoupled_square_spectrum_finite_sampling_candidate_node :=
    D.conclusion_decoupled_square_spectrum_finite_sampling_node
  conclusion_decoupled_square_spectrum_finite_sampling_candidate_multiplicity :=
    D.conclusion_decoupled_square_spectrum_finite_sampling_multiplicity
  conclusion_decoupled_square_spectrum_finite_sampling_candidate_oddWeight :=
    D.conclusion_decoupled_square_spectrum_finite_sampling_oddWeight
  conclusion_decoupled_square_spectrum_finite_sampling_candidate_sample :=
    D.conclusion_decoupled_square_spectrum_finite_sampling_sample

/-- Agreement of the first `2*K` scalar samples. -/
def conclusion_decoupled_square_spectrum_finite_sampling_first_samples_agree
    (D : conclusion_decoupled_square_spectrum_finite_sampling_data)
    (E :
      conclusion_decoupled_square_spectrum_finite_sampling_candidate
        D.conclusion_decoupled_square_spectrum_finite_sampling_K) : Prop :=
  ∀ q : Fin (2 * D.conclusion_decoupled_square_spectrum_finite_sampling_K),
    E.conclusion_decoupled_square_spectrum_finite_sampling_candidate_sample q.1 =
      D.conclusion_decoupled_square_spectrum_finite_sampling_sample q.1

/-- Statement package for `thm:conclusion-decoupled-square-spectrum-finite-sampling`. -/
noncomputable def conclusion_decoupled_square_spectrum_finite_sampling_statement
    (D : conclusion_decoupled_square_spectrum_finite_sampling_data) : Prop :=
  conclusion_decoupled_square_spectrum_finite_sampling_candidate_even_decomposition
      (conclusion_decoupled_square_spectrum_finite_sampling_data_candidate D) ∧
    conclusion_decoupled_square_spectrum_finite_sampling_candidate_odd_decomposition
      (conclusion_decoupled_square_spectrum_finite_sampling_data_candidate D) ∧
      ∀ E :
        conclusion_decoupled_square_spectrum_finite_sampling_candidate
          D.conclusion_decoupled_square_spectrum_finite_sampling_K,
        conclusion_decoupled_square_spectrum_finite_sampling_first_samples_agree D E →
        conclusion_decoupled_square_spectrum_finite_sampling_candidate_even_decomposition E →
        conclusion_decoupled_square_spectrum_finite_sampling_candidate_odd_decomposition E →
          E.conclusion_decoupled_square_spectrum_finite_sampling_candidate_node =
              D.conclusion_decoupled_square_spectrum_finite_sampling_node ∧
            E.conclusion_decoupled_square_spectrum_finite_sampling_candidate_multiplicity =
              D.conclusion_decoupled_square_spectrum_finite_sampling_multiplicity ∧
              E.conclusion_decoupled_square_spectrum_finite_sampling_candidate_oddWeight =
                D.conclusion_decoupled_square_spectrum_finite_sampling_oddWeight

/-- Paper label: `thm:conclusion-decoupled-square-spectrum-finite-sampling`. -/
theorem paper_conclusion_decoupled_square_spectrum_finite_sampling
    (D : conclusion_decoupled_square_spectrum_finite_sampling_data) :
    conclusion_decoupled_square_spectrum_finite_sampling_statement D := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    exact D.conclusion_decoupled_square_spectrum_finite_sampling_even_moment_identity n
  · intro n
    exact D.conclusion_decoupled_square_spectrum_finite_sampling_odd_moment_identity n
  · intro E hfirst heven hodd
    exact
      D.conclusion_decoupled_square_spectrum_finite_sampling_prony_recovery E
        (fun n hn => hfirst ⟨n, hn⟩) heven hodd

end Omega.Conclusion
