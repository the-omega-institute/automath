import Mathlib.Tactic

namespace Omega.POM

noncomputable section

/-- Rational torus phase data encoded by coordinate numerators and exact positive
denominators.  A positive integer eliminates the phase exactly when it is divisible by every
coordinate denominator. -/
structure pom_anom_torus_phase_elimination_data where
  pom_anom_torus_phase_elimination_rank : ℕ
  pom_anom_torus_phase_elimination_numerator :
    Fin pom_anom_torus_phase_elimination_rank → ℤ
  pom_anom_torus_phase_elimination_denominator :
    Fin pom_anom_torus_phase_elimination_rank → ℕ
  pom_anom_torus_phase_elimination_denominator_pos :
    ∀ j, 0 < pom_anom_torus_phase_elimination_denominator j

namespace pom_anom_torus_phase_elimination_data

/-- Coordinatewise finite-cover elimination. -/
def pom_anom_torus_phase_elimination_eliminates
    (D : pom_anom_torus_phase_elimination_data) (q : ℕ) : Prop :=
  ∀ j, D.pom_anom_torus_phase_elimination_denominator j ∣ q

/-- The least common multiple of the rational coordinate denominators. -/
def pom_anom_torus_phase_elimination_minimal_order
    (D : pom_anom_torus_phase_elimination_data) : ℕ :=
  Finset.lcm Finset.univ D.pom_anom_torus_phase_elimination_denominator

/-- Elimination is equivalent to divisibility by the denominator lcm, which is therefore the
minimal positive eliminating order in the divisibility preorder. -/
def elimination_iff_and_minimal_order (D : pom_anom_torus_phase_elimination_data) : Prop :=
  (∀ q : ℕ,
      D.pom_anom_torus_phase_elimination_eliminates q ↔
        D.pom_anom_torus_phase_elimination_minimal_order ∣ q) ∧
    (∀ j,
      D.pom_anom_torus_phase_elimination_denominator j ∣
        D.pom_anom_torus_phase_elimination_minimal_order) ∧
      ∀ q : ℕ,
        D.pom_anom_torus_phase_elimination_eliminates q →
          D.pom_anom_torus_phase_elimination_minimal_order ∣ q

end pom_anom_torus_phase_elimination_data

open pom_anom_torus_phase_elimination_data

/-- Paper label: `cor:pom-anom-torus-phase-elimination`.  Coordinatewise torsion reduces to
divisibility by the rational denominators; the eliminating order is their lcm. -/
theorem paper_pom_anom_torus_phase_elimination
    (D : pom_anom_torus_phase_elimination_data) :
    D.elimination_iff_and_minimal_order := by
  constructor
  · intro q
    constructor
    · intro hq
      exact Finset.lcm_dvd (fun j _ => hq j)
    · intro hq j
      exact dvd_trans (Finset.dvd_lcm (Finset.mem_univ j)) hq
  · constructor
    · intro j
      exact Finset.dvd_lcm (Finset.mem_univ j)
    · intro q hq
      exact Finset.lcm_dvd (fun j _ => hq j)

end

end Omega.POM
