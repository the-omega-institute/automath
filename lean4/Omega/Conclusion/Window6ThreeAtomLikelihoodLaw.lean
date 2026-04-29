import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

noncomputable section

/-- Multiplicities appearing in the audited window-`6` three-atom law. -/
def conclusion_window6_three_atom_likelihood_law_support : Finset ℕ :=
  {2, 3, 4}

/-- Histogram counts for multiplicities `2`, `3`, and `4`. -/
def conclusion_window6_three_atom_likelihood_law_count : ℕ → ℕ
  | 2 => 8
  | 3 => 4
  | 4 => 9
  | _ => 0

/-- The total number of output fibers in the audited window-`6` histogram. -/
def conclusion_window6_three_atom_likelihood_law_total_fibers : ℕ :=
  21

/-- The total binary microstate mass in the audited window-`6` histogram. -/
def conclusion_window6_three_atom_likelihood_law_total_microstates : ℕ :=
  64

/-- Likelihood ratio `p_6 / u_6` attached to a fiber multiplicity. -/
def conclusion_window6_three_atom_likelihood_law_likelihood (m : ℕ) : ℚ :=
  (conclusion_window6_three_atom_likelihood_law_total_fibers : ℚ) * (m : ℚ) /
    (conclusion_window6_three_atom_likelihood_law_total_microstates : ℚ)

/-- Reference-law weight of a multiplicity atom. -/
def conclusion_window6_three_atom_likelihood_law_weight (m : ℕ) : ℝ :=
  (conclusion_window6_three_atom_likelihood_law_count m : ℝ) /
    (conclusion_window6_three_atom_likelihood_law_total_fibers : ℝ)

/-- Finite three-atom `f`-divergence induced by the window-`6` likelihood law. -/
def conclusion_window6_three_atom_likelihood_law_fDivergence (f : ℚ → ℝ) : ℝ :=
  Finset.sum conclusion_window6_three_atom_likelihood_law_support fun m =>
    conclusion_window6_three_atom_likelihood_law_weight m *
      f (conclusion_window6_three_atom_likelihood_law_likelihood m)

/-- Paper label: `thm:conclusion-window6-three-atom-likelihood-law`. -/
theorem paper_conclusion_window6_three_atom_likelihood_law (f : ℚ → ℝ) :
    conclusion_window6_three_atom_likelihood_law_likelihood 2 = (21 : ℚ) / 32 ∧
      conclusion_window6_three_atom_likelihood_law_likelihood 3 = (63 : ℚ) / 64 ∧
      conclusion_window6_three_atom_likelihood_law_likelihood 4 = (21 : ℚ) / 16 ∧
      conclusion_window6_three_atom_likelihood_law_fDivergence f =
        (8 : ℝ) / 21 * f (21 / 32) + (4 : ℝ) / 21 * f (63 / 64) +
          (9 : ℝ) / 21 * f (21 / 16) := by
  norm_num [conclusion_window6_three_atom_likelihood_law_likelihood,
    conclusion_window6_three_atom_likelihood_law_total_fibers,
    conclusion_window6_three_atom_likelihood_law_total_microstates,
    conclusion_window6_three_atom_likelihood_law_fDivergence,
    conclusion_window6_three_atom_likelihood_law_support,
    conclusion_window6_three_atom_likelihood_law_weight,
    conclusion_window6_three_atom_likelihood_law_count]
  ring

end

end Omega.Conclusion
