import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete sequence-level data for the Bohr--Mellin multiscale criterion.  The three recorded
implications represent the explicit-formula and nondegeneracy inputs used to pass between RH,
Bohr almost-periodic modeling, and uniform boundedness. -/
structure xi_mellin_scale_bohr_rh_equivalence_data where
  xi_mellin_scale_bohr_rh_equivalence_scaleDefect : ℕ → ℤ
  xi_mellin_scale_bohr_rh_equivalence_bohrProfile : ℕ → ℤ
  xi_mellin_scale_bohr_rh_equivalence_rh_to_bohr_model :
    (∀ m, xi_mellin_scale_bohr_rh_equivalence_scaleDefect m = 0) →
      ∀ m,
        xi_mellin_scale_bohr_rh_equivalence_bohrProfile m =
          xi_mellin_scale_bohr_rh_equivalence_scaleDefect m
  xi_mellin_scale_bohr_rh_equivalence_bohr_model_to_bounded :
    (∀ m,
        xi_mellin_scale_bohr_rh_equivalence_bohrProfile m =
          xi_mellin_scale_bohr_rh_equivalence_scaleDefect m) →
      ∃ C : ℕ,
        ∀ m, Int.natAbs (xi_mellin_scale_bohr_rh_equivalence_scaleDefect m) ≤ C
  xi_mellin_scale_bohr_rh_equivalence_bounded_to_rh :
    (∃ C : ℕ,
        ∀ m, Int.natAbs (xi_mellin_scale_bohr_rh_equivalence_scaleDefect m) ≤ C) →
      ∀ m, xi_mellin_scale_bohr_rh_equivalence_scaleDefect m = 0

namespace xi_mellin_scale_bohr_rh_equivalence_data

/-- RH-facing predicate: every scale defect vanishes. -/
def xi_mellin_scale_bohr_rh_equivalence_rh
    (D : xi_mellin_scale_bohr_rh_equivalence_data) : Prop :=
  ∀ m, D.xi_mellin_scale_bohr_rh_equivalence_scaleDefect m = 0

/-- Uniform boundedness of the multiscale Mellin defects. -/
def xi_mellin_scale_bohr_rh_equivalence_bounded
    (D : xi_mellin_scale_bohr_rh_equivalence_data) : Prop :=
  ∃ C : ℕ, ∀ m, Int.natAbs (D.xi_mellin_scale_bohr_rh_equivalence_scaleDefect m) ≤ C

/-- Bohr-model predicate for the packaged scale profile. -/
def xi_mellin_scale_bohr_rh_equivalence_bohr_model
    (D : xi_mellin_scale_bohr_rh_equivalence_data) : Prop :=
  ∀ m,
    D.xi_mellin_scale_bohr_rh_equivalence_bohrProfile m =
      D.xi_mellin_scale_bohr_rh_equivalence_scaleDefect m

end xi_mellin_scale_bohr_rh_equivalence_data

open xi_mellin_scale_bohr_rh_equivalence_data

/-- Paper label: `thm:xi-mellin-scale-bohr-rh-equivalence`. -/
theorem paper_xi_mellin_scale_bohr_rh_equivalence
    (D : xi_mellin_scale_bohr_rh_equivalence_data) :
    D.xi_mellin_scale_bohr_rh_equivalence_rh ↔
      D.xi_mellin_scale_bohr_rh_equivalence_bounded ∧
        D.xi_mellin_scale_bohr_rh_equivalence_bohr_model := by
  constructor
  · intro hRH
    have hBohr : D.xi_mellin_scale_bohr_rh_equivalence_bohr_model :=
      D.xi_mellin_scale_bohr_rh_equivalence_rh_to_bohr_model hRH
    exact
      ⟨D.xi_mellin_scale_bohr_rh_equivalence_bohr_model_to_bounded hBohr, hBohr⟩
  · intro h
    exact D.xi_mellin_scale_bohr_rh_equivalence_bounded_to_rh h.1

end Omega.Zeta
