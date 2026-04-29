import Mathlib.Tactic
import Omega.Conclusion.Window6RootSplitDegeneracyCrossTable
import Omega.FoldResidualTime.Window6FixedFreezingLaw

namespace Omega.Conclusion

open Omega.FoldResidualTime

noncomputable section

/-- Window-6 escort denominator from the audited `2:8, 3:4, 4:9` histogram. -/
def conclusion_window6_minshell_escort_sector_law_denominator (q : ℕ) : ℝ :=
  9 * (4 : ℝ) ^ q + 4 * (3 : ℝ) ^ q + 8 * (2 : ℝ) ^ q

/-- Escort mass of the minimal `d = 2` shell. -/
def conclusion_window6_minshell_escort_sector_law_min_shell_mass (q : ℕ) : ℝ :=
  8 * (2 : ℝ) ^ q / conclusion_window6_minshell_escort_sector_law_denominator q

/-- Boundary part of the minimal shell. -/
def conclusion_window6_minshell_escort_sector_law_boundary_mass (q : ℕ) : ℝ :=
  3 * (2 : ℝ) ^ q / conclusion_window6_minshell_escort_sector_law_denominator q

/-- Cyclic part inside the minimal shell. -/
def conclusion_window6_minshell_escort_sector_law_cyclic_min_mass (q : ℕ) : ℝ :=
  5 * (2 : ℝ) ^ q / conclusion_window6_minshell_escort_sector_law_denominator q

/-- Total cyclic-sector escort mass. -/
def conclusion_window6_minshell_escort_sector_law_cyclic_mass (q : ℕ) : ℝ :=
  (9 * (4 : ℝ) ^ q + 4 * (3 : ℝ) ^ q + 5 * (2 : ℝ) ^ q) /
    conclusion_window6_minshell_escort_sector_law_denominator q

/-- Boundary conditional mass inside the minimal shell. -/
def conclusion_window6_minshell_escort_sector_law_boundary_conditional (q : ℕ) : ℝ :=
  conclusion_window6_minshell_escort_sector_law_boundary_mass q /
    conclusion_window6_minshell_escort_sector_law_min_shell_mass q

/-- Cyclic conditional mass inside the minimal shell. -/
def conclusion_window6_minshell_escort_sector_law_cyclic_conditional (q : ℕ) : ℝ :=
  conclusion_window6_minshell_escort_sector_law_cyclic_min_mass q /
    conclusion_window6_minshell_escort_sector_law_min_shell_mass q

/-- Concrete statement package for the window-6 minimal-shell escort sector law. -/
def conclusion_window6_minshell_escort_sector_law_statement : Prop :=
  (∀ q : ℕ,
    conclusion_window6_minshell_escort_sector_law_denominator q =
      window6FiberMomentSum q) ∧
  conclusion_window6_root_split_degeneracy_cross_table_statement ∧
  (∀ q : ℕ,
    conclusion_window6_minshell_escort_sector_law_min_shell_mass q =
      8 * (2 : ℝ) ^ q / conclusion_window6_minshell_escort_sector_law_denominator q) ∧
  (∀ q : ℕ,
    conclusion_window6_minshell_escort_sector_law_boundary_mass q =
      3 * (2 : ℝ) ^ q / conclusion_window6_minshell_escort_sector_law_denominator q) ∧
  (∀ q : ℕ,
    conclusion_window6_minshell_escort_sector_law_cyclic_min_mass q =
      5 * (2 : ℝ) ^ q / conclusion_window6_minshell_escort_sector_law_denominator q) ∧
  (∀ q : ℕ,
    conclusion_window6_minshell_escort_sector_law_cyclic_mass q =
      (9 * (4 : ℝ) ^ q + 4 * (3 : ℝ) ^ q + 5 * (2 : ℝ) ^ q) /
        conclusion_window6_minshell_escort_sector_law_denominator q) ∧
  (∀ q : ℕ,
    conclusion_window6_minshell_escort_sector_law_boundary_conditional q = 3 / 8) ∧
  (∀ q : ℕ,
    conclusion_window6_minshell_escort_sector_law_cyclic_conditional q = 5 / 8)

private lemma conclusion_window6_minshell_escort_sector_law_denominator_pos (q : ℕ) :
    0 < conclusion_window6_minshell_escort_sector_law_denominator q := by
  unfold conclusion_window6_minshell_escort_sector_law_denominator
  positivity

/-- Paper label: `prop:conclusion-window6-minshell-escort-sector-law`. -/
theorem paper_conclusion_window6_minshell_escort_sector_law :
    conclusion_window6_minshell_escort_sector_law_statement := by
  refine ⟨?_, paper_conclusion_window6_root_split_degeneracy_cross_table, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q
    unfold conclusion_window6_minshell_escort_sector_law_denominator window6FiberMomentSum
    ring
  · intro q
    rfl
  · intro q
    rfl
  · intro q
    rfl
  · intro q
    rfl
  · intro q
    unfold conclusion_window6_minshell_escort_sector_law_boundary_conditional
      conclusion_window6_minshell_escort_sector_law_boundary_mass
      conclusion_window6_minshell_escort_sector_law_min_shell_mass
    have hden : conclusion_window6_minshell_escort_sector_law_denominator q ≠ 0 :=
      (conclusion_window6_minshell_escort_sector_law_denominator_pos q).ne'
    have hpow : ((2 : ℝ) ^ q) ≠ 0 := by positivity
    field_simp [hden, hpow]
  · intro q
    unfold conclusion_window6_minshell_escort_sector_law_cyclic_conditional
      conclusion_window6_minshell_escort_sector_law_cyclic_min_mass
      conclusion_window6_minshell_escort_sector_law_min_shell_mass
    have hden : conclusion_window6_minshell_escort_sector_law_denominator q ≠ 0 :=
      (conclusion_window6_minshell_escort_sector_law_denominator_pos q).ne'
    have hpow : ((2 : ℝ) ^ q) ≠ 0 := by positivity
    field_simp [hden, hpow]

end

end Omega.Conclusion
