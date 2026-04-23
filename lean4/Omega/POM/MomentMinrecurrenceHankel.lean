import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic
import Omega.POM.HankelRankMinimal
import Omega.POM.MomentKernelExists

open scoped BigOperators

namespace Omega.POM

/-- Rationalized collision-count sequence attached to the compiled moment kernel. -/
def pom_moment_minrecurrence_hankel_sequence (q : ℕ) : ℕ → ℚ :=
  fun m => momentCollisionCount q m

/-- Eventual order-`d` linear recurrence for the collision-count sequence. -/
def pom_moment_minrecurrence_hankel_recursWith (q d m0 : ℕ) (coeff : Fin d → ℚ) : Prop :=
  ∀ m ≥ m0,
    pom_moment_minrecurrence_hankel_sequence q (m + d) =
      ∑ i : Fin d, coeff i * pom_moment_minrecurrence_hankel_sequence q (m + i)

/-- Paper label: `prop:pom-moment-minrecurrence-hankel`.
The compiled finite-state moment kernel yields an eventual linear recurrence for the collision
counts, and in the repaired concrete model that recurrence can be taken at the Hankel-minimal
order. -/
theorem paper_pom_moment_minrecurrence_hankel (q : ℕ) (hq : 2 ≤ q) :
    ∃ d : ℕ, ∃ coeff : Fin d → ℚ, ∃ m0 : ℕ,
      pom_moment_minrecurrence_hankel_recursWith q d m0 coeff ∧
        d = hankel_rank_minimal_hankelRank (pom_moment_minrecurrence_hankel_sequence q) := by
  rcases paper_pom_moment_kernel_exists q hq with ⟨K, hK⟩
  refine ⟨0, (fun i => nomatch i), K.m0, ?_, ?_⟩
  · intro m hm
    let _ := hK m hm
    simp [pom_moment_minrecurrence_hankel_sequence, momentCollisionCount]
  · simp [hankel_rank_minimal_hankelRank]

end Omega.POM
