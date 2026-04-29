import Mathlib

namespace Omega.POM

open Finset
open scoped BigOperators

/-- Inclusion-exclusion higher cross anomaly on the Boolean lattice of coordinate subsets.
    `prop:pom-pairwise-cross-anom-insufficient` -/
def pom_pairwise_cross_anom_insufficient_higher_cross_anomaly {k : Nat}
    (L : Finset (Fin k) → ℝ) (S : Finset (Fin k)) : ℝ :=
  Finset.sum S.powerset fun T => (-1 : ℝ) ^ (S.card - T.card) * L T

/-- The explicit three-axis counterexample with only a genuine triple interaction has vanishing
pairwise anomalies but nonzero triple anomaly. `prop:pom-pairwise-cross-anom-insufficient` -/
theorem paper_pom_pairwise_cross_anom_insufficient :
    ∃ L : Finset (Fin 3) → ℝ,
      (∀ S : Finset (Fin 3), S.card = 2 →
        pom_pairwise_cross_anom_insufficient_higher_cross_anomaly L S = 0) ∧
      pom_pairwise_cross_anom_insufficient_higher_cross_anomaly L Finset.univ ≠ 0 := by
  classical
  refine ⟨fun S => if S = (Finset.univ : Finset (Fin 3)) then 1 else 0, ?_⟩
  constructor
  · intro S hS
    unfold pom_pairwise_cross_anom_insufficient_higher_cross_anomaly
    refine Finset.sum_eq_zero ?_
    intro T hT
    have hsub : T ⊆ S := Finset.mem_powerset.mp hT
    have hTne : T ≠ (Finset.univ : Finset (Fin 3)) := by
      intro hEq
      have hle : T.card ≤ S.card := Finset.card_le_card hsub
      simp [hEq, hS] at hle
    simp [hTne]
  · unfold pom_pairwise_cross_anom_insufficient_higher_cross_anomaly
    have huniv_mem :
        (Finset.univ : Finset (Fin 3)) ∈ (Finset.univ : Finset (Fin 3)).powerset := by
      simp
    rw [Finset.sum_eq_single_of_mem (a := (Finset.univ : Finset (Fin 3))) huniv_mem]
    · norm_num
    · intro T hT hTne
      simp [hTne]

end Omega.POM
