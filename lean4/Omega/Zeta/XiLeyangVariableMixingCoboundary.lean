import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Concrete finite Lee--Yang variable-mixing data. -/
structure paper_xi_leyang_variable_mixing_coboundary_Data where
  N : ℕ
  kappa : ℝ
  Y : Fin N → ℝ

/-- Potential whose coboundary gives the mixing defect. -/
def xi_leyang_variable_mixing_coboundary_potential
    (D : paper_xi_leyang_variable_mixing_coboundary_Data) (n : Fin D.N) : ℝ :=
  -D.kappa * (D.Y n) ^ 2

/-- First-order variable-mixing defect. -/
def xi_leyang_variable_mixing_coboundary_defect
    (D : paper_xi_leyang_variable_mixing_coboundary_Data) (n m : Fin D.N) : ℝ :=
  -D.kappa * ((D.Y n) ^ 2 - (D.Y m) ^ 2)

/-- Concrete statement of the coboundary identity, the four-term cancellation, and the vanishing
of every closed telescoping loop. -/
def paper_xi_leyang_variable_mixing_coboundary_statement
    (D : paper_xi_leyang_variable_mixing_coboundary_Data) : Prop :=
  (∀ n m,
      xi_leyang_variable_mixing_coboundary_defect D n m =
        xi_leyang_variable_mixing_coboundary_potential D n -
          xi_leyang_variable_mixing_coboundary_potential D m) ∧
    (∀ n m p q,
      xi_leyang_variable_mixing_coboundary_defect D n m +
          xi_leyang_variable_mixing_coboundary_defect D p q -
          xi_leyang_variable_mixing_coboundary_defect D n q -
          xi_leyang_variable_mixing_coboundary_defect D p m =
        0) ∧
    (∀ gamma : ℕ → Fin D.N, ∀ k : ℕ, gamma k = gamma 0 →
      Finset.sum (Finset.range k)
          (fun j => xi_leyang_variable_mixing_coboundary_defect D (gamma j) (gamma (j + 1))) = 0)

lemma xi_leyang_variable_mixing_coboundary_defect_eq_potential_diff
    (D : paper_xi_leyang_variable_mixing_coboundary_Data) (n m : Fin D.N) :
    xi_leyang_variable_mixing_coboundary_defect D n m =
      xi_leyang_variable_mixing_coboundary_potential D n -
        xi_leyang_variable_mixing_coboundary_potential D m := by
  simp [xi_leyang_variable_mixing_coboundary_defect, xi_leyang_variable_mixing_coboundary_potential]
  ring

lemma xi_leyang_variable_mixing_coboundary_telescope
    (D : paper_xi_leyang_variable_mixing_coboundary_Data) (gamma : ℕ → Fin D.N) :
    ∀ k : ℕ,
      Finset.sum (Finset.range k)
          (fun j => xi_leyang_variable_mixing_coboundary_defect D (gamma j) (gamma (j + 1))) =
        xi_leyang_variable_mixing_coboundary_potential D (gamma 0) -
          xi_leyang_variable_mixing_coboundary_potential D (gamma k)
  | 0 => by simp
  | k + 1 => by
      rw [Finset.sum_range_succ, xi_leyang_variable_mixing_coboundary_telescope D gamma k,
        xi_leyang_variable_mixing_coboundary_defect_eq_potential_diff]
      ring

/-- Paper label: `prop:xi-leyang-variable-mixing-coboundary`. Writing the variable-mixing defect
as the difference of the quadratic potential `U_n = -kappa * Y_n^2` makes both the four-term
identity and the closed-loop cancellation immediate telescoping consequences. -/
theorem paper_xi_leyang_variable_mixing_coboundary
    (D : paper_xi_leyang_variable_mixing_coboundary_Data) :
    paper_xi_leyang_variable_mixing_coboundary_statement D := by
  refine ⟨?_, ?_, ?_⟩
  · intro n m
    exact xi_leyang_variable_mixing_coboundary_defect_eq_potential_diff D n m
  · intro n m p q
    repeat rw [xi_leyang_variable_mixing_coboundary_defect_eq_potential_diff]
    ring
  · intro gamma k hk
    rw [xi_leyang_variable_mixing_coboundary_telescope D gamma k, hk]
    ring

end Omega.Zeta
