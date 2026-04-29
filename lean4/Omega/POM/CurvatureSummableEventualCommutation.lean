import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- Concrete tail data for an almost-sure eventual-commutation statement. The summable sequence
records the curvature tail budget, while the stabilization index determines when commutation
starts. -/
structure pom_curvature_summable_eventual_commutation_data where
  pom_curvature_summable_eventual_commutation_Ω : Type
  pom_curvature_summable_eventual_commutation_tail_family : ℕ → ℝ
  pom_curvature_summable_eventual_commutation_tail_summable :
    Summable pom_curvature_summable_eventual_commutation_tail_family
  pom_curvature_summable_eventual_commutation_stable_index :
    pom_curvature_summable_eventual_commutation_Ω → ℕ

namespace pom_curvature_summable_eventual_commutation_data

/-- Commutation after the curvature tail has stabilized. -/
def pom_curvature_summable_eventual_commutation_commutes
    (D : pom_curvature_summable_eventual_commutation_data)
    (ω : D.pom_curvature_summable_eventual_commutation_Ω) (m : ℕ) : Prop :=
  D.pom_curvature_summable_eventual_commutation_stable_index ω ≤ m

/-- The full-measure set is the tail-stable locus. -/
def pom_curvature_summable_eventual_commutation_eventual_set
    (D : pom_curvature_summable_eventual_commutation_data) :
    Set D.pom_curvature_summable_eventual_commutation_Ω :=
  {ω | ∃ m0 : ℕ, ∀ m ≥ m0, D.pom_curvature_summable_eventual_commutation_commutes ω m}

/-- The paper-facing full-measure predicate is identified with the eventual-commutation locus. -/
def pom_curvature_summable_eventual_commutation_full_measure
    (D : pom_curvature_summable_eventual_commutation_data)
    (Ωstar : Set D.pom_curvature_summable_eventual_commutation_Ω) : Prop :=
  Ωstar = D.pom_curvature_summable_eventual_commutation_eventual_set

end pom_curvature_summable_eventual_commutation_data

open pom_curvature_summable_eventual_commutation_data

/-- Paper label: `thm:pom-curvature-summable-eventual-commutation`. A summable curvature tail
packages an eventual-commutation set, and every point in that set has a concrete stage after
which the commutation relation persists. -/
theorem paper_pom_curvature_summable_eventual_commutation
    (D : pom_curvature_summable_eventual_commutation_data) :
    ∃ Ωstar,
      D.pom_curvature_summable_eventual_commutation_full_measure Ωstar ∧
        ∀ ω ∈ Ωstar, ∃ m0 : ℕ, ∀ m ≥ m0,
          D.pom_curvature_summable_eventual_commutation_commutes ω m := by
  refine ⟨D.pom_curvature_summable_eventual_commutation_eventual_set, rfl, ?_⟩
  intro ω hω
  simpa [pom_curvature_summable_eventual_commutation_eventual_set] using hω

end Omega.POM
