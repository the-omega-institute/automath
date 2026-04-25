import Mathlib.Tactic
import Omega.Conclusion.CdimPhaseCompressionPowerLaw

namespace Omega.Conclusion

/-- Concrete wrapper for extracting an approximate-annihilator integer from every phase-compressed
crowding witness. The finite box/cell data are provided stage-by-stage by the existing power-law
theorem, and the chapter-local `difference` map converts a close pair into a nonzero integer
approximate annihilator. -/
structure conclusion_phase_compression_infinite_approximate_annihilators_data where
  conclusion_phase_compression_infinite_approximate_annihilators_core :
    ℕ → conclusion_cdim_phase_compression_power_law_data
  conclusion_phase_compression_infinite_approximate_annihilators_difference :
    ∀ N,
      (conclusion_phase_compression_infinite_approximate_annihilators_core N).α →
        (conclusion_phase_compression_infinite_approximate_annihilators_core N).α → ℤ
  conclusion_phase_compression_infinite_approximate_annihilators_error : ℕ → ℤ → ℝ
  conclusion_phase_compression_infinite_approximate_annihilators_difference_ne_zero :
    ∀ N
      {u v :
        (conclusion_phase_compression_infinite_approximate_annihilators_core N).α},
      u ≠ v →
        conclusion_phase_compression_infinite_approximate_annihilators_difference N u v ≠ 0
  conclusion_phase_compression_infinite_approximate_annihilators_witness_bound :
    ∀ N
      {u v :
        (conclusion_phase_compression_infinite_approximate_annihilators_core N).α},
      (conclusion_phase_compression_infinite_approximate_annihilators_core N).torusDist
          ((conclusion_phase_compression_infinite_approximate_annihilators_core N).phi u)
          ((conclusion_phase_compression_infinite_approximate_annihilators_core N).phi v) ≤
        2 *
          (((conclusion_phase_compression_infinite_approximate_annihilators_core N).N + 1 : ℝ) ^
            (-((conclusion_phase_compression_infinite_approximate_annihilators_core N).r : ℝ) /
              (conclusion_phase_compression_infinite_approximate_annihilators_core N).d)) →
        |conclusion_phase_compression_infinite_approximate_annihilators_error N
            (conclusion_phase_compression_infinite_approximate_annihilators_difference N u v)| ≤
          2 *
            (((conclusion_phase_compression_infinite_approximate_annihilators_core N).N + 1 : ℝ) ^
              (-((conclusion_phase_compression_infinite_approximate_annihilators_core N).r : ℝ) /
                (conclusion_phase_compression_infinite_approximate_annihilators_core N).d))

/-- Infinite approximate-annihilator sequence forced by phase compression. -/
def conclusion_phase_compression_infinite_approximate_annihilators_statement
    (D : conclusion_phase_compression_infinite_approximate_annihilators_data) : Prop :=
  ∃ k : ℕ → ℤ,
    ∀ N,
      k N ≠ 0 ∧
        |D.conclusion_phase_compression_infinite_approximate_annihilators_error N (k N)| ≤
          2 *
            (((D.conclusion_phase_compression_infinite_approximate_annihilators_core N).N + 1 : ℝ) ^
              (-((D.conclusion_phase_compression_infinite_approximate_annihilators_core N).r : ℝ) /
                (D.conclusion_phase_compression_infinite_approximate_annihilators_core N).d))

/-- Paper label: `thm:conclusion-phase-compression-infinite-approximate-annihilators`. Applying
the power-law crowding theorem at every stage `N` yields two distinct box points in one torus
cell; converting each pair into its integer difference produces an infinite sequence of nonzero
approximate annihilators with the advertised power-law error bound. -/
theorem paper_conclusion_phase_compression_infinite_approximate_annihilators
    (D : conclusion_phase_compression_infinite_approximate_annihilators_data) :
    conclusion_phase_compression_infinite_approximate_annihilators_statement D := by
  classical
  choose u v hu hv huv hbound using
    fun N =>
      paper_conclusion_cdim_phase_compression_power_law
        (D.conclusion_phase_compression_infinite_approximate_annihilators_core N)
  refine ⟨fun N =>
    D.conclusion_phase_compression_infinite_approximate_annihilators_difference N (u N) (v N), ?_⟩
  intro N
  refine
    ⟨D.conclusion_phase_compression_infinite_approximate_annihilators_difference_ne_zero N
        (huv N),
      ?_⟩
  exact
    D.conclusion_phase_compression_infinite_approximate_annihilators_witness_bound N (hbound N)

end Omega.Conclusion
