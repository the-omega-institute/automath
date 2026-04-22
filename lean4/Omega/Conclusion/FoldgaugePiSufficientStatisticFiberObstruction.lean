import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
import Omega.POM.SufficientStatisticResidualNoninvertibility

namespace Omega.Conclusion

open Omega.POM.SufficientStatisticResidualNoninvertibility

/-- The fold-`π` fiber multiplicity closed form attached to a path decomposition
`Γₓ ≃ ⨆ᵢ P_{ℓᵢ}`. -/
def conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_fiber_card
    (L : List ℕ) : ℕ :=
  (L.map fun ell => Nat.fib (ell + 2)).prod

/-- The inverse-substitution degree bound `∑ᵢ ⌈ℓᵢ / 2⌉`, written on naturals as
`∑ᵢ (ℓᵢ + 1) / 2`. -/
def conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_degree
    (L : List ℕ) : ℕ :=
  (L.map fun ell => (ell + 1) / 2).sum

/-- The fold/output pair map on a fixed fiber, modeled as a constant fold label together with the
residual statistic. -/
def conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_pair_map
    (L : List ℕ)
    (ℛ :
      Fin (conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_fiber_card L) →
        Fin (conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_degree L + 1)) :
    Fin (conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_fiber_card L) →
      Fin 1 × Fin (conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_degree L + 1) :=
  fun ω => (0, ℛ ω)

/-- Concrete fold-`π` sufficient-statistic obstruction package: the fiber multiplicity and the
inverse-substitution degree have the Fibonacci/ceiling closed forms, and any residual taking only
`deg Zₓ + 1` values forces a noninjective fold/residual pairing once the fiber is larger. -/
def conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_statement : Prop :=
  ∀ L : List ℕ,
    conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_fiber_card L =
        (L.map fun ell => Nat.fib (ell + 2)).prod ∧
      conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_degree L =
        (L.map fun ell => (ell + 1) / 2).sum ∧
      ∀ ℛ :
          Fin (conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_fiber_card L) →
            Fin (conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_degree L + 1),
        conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_degree L + 1 <
            conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_fiber_card L →
          ¬ Function.Injective
            (conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_pair_map L ℛ)

lemma conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_residual_injective_of_pair
    {L : List ℕ}
    {ℛ :
      Fin (conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_fiber_card L) →
        Fin (conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_degree L + 1)}
    (hinj :
      Function.Injective
        (conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_pair_map L ℛ)) :
    Function.Injective ℛ := by
  intro ω₁ ω₂ hω
  apply hinj
  simp [conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_pair_map, hω]

/-- Paper label: `thm:conclusion-foldgauge-pi-sufficient-statistic-fiber-obstruction`. -/
theorem paper_conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction :
    conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_statement := by
  intro L
  refine ⟨rfl, rfl, ?_⟩
  intro ℛ hbig
  intro hinj
  have hresidual :
      Function.Injective ℛ :=
    conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_residual_injective_of_pair hinj
  exact
    (paper_pom_sufficient_statistic_residual_noninvertibility
      (conclusion_foldgauge_pi_sufficient_statistic_fiber_obstruction_degree L) ℛ
      (by simpa using hbig)) hresidual

end Omega.Conclusion
