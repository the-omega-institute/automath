import Mathlib

namespace Omega.POM

open Finset
open scoped BigOperators

/-- Inclusion-exclusion higher cross anomaly used by the axis-decomposability audit.
    `thm:pom-axis-decomposability-iff` -/
def pom_axis_decomposability_iff_higher_cross_anomaly {k : Nat}
    (L : Finset (Fin k) → ℝ) (S : Finset (Fin k)) : ℝ :=
  Finset.sum S.powerset fun T => (-1 : ℝ) ^ (S.card - T.card) * L T

/-- The requested publication signature is false without an additional normalization such as
`L ∅ = 0`: for `k = 1`, the anomaly condition is vacuous, but axis decomposability still forces
`L ∅ = 0`. This witness justifies the paper-side partial annotation. -/
theorem pom_axis_decomposability_iff_signature_false :
    ¬ ∀ L : Finset (Fin 1) → ℝ,
        ((∃ ell : Fin 1 → ℝ, ∀ S : Finset (Fin 1), L S = Finset.sum S ell) ↔
          (∀ S : Finset (Fin 1), 2 <= S.card →
            pom_axis_decomposability_iff_higher_cross_anomaly L S = 0)) := by
  intro hAll
  let L : Finset (Fin 1) → ℝ := fun S => if S = ∅ then 1 else 0
  have hiff := hAll L
  have hRight : ∀ S : Finset (Fin 1), 2 <= S.card →
      pom_axis_decomposability_iff_higher_cross_anomaly L S = 0 := by
    intro S hS
    have hsubset : S ⊆ ({0} : Finset (Fin 1)) := by
      intro x hx
      fin_cases x
      simp
    have hle : S.card ≤ 1 := by
      simpa using (Finset.card_le_card hsubset : S.card ≤ ({0} : Finset (Fin 1)).card)
    have hFalse : False := by omega
    exact False.elim hFalse
  have hLeft : ∃ ell : Fin 1 → ℝ, ∀ S : Finset (Fin 1), L S = Finset.sum S ell := hiff.mpr hRight
  rcases hLeft with ⟨ell, hell⟩
  have hEmpty : L ∅ = Finset.sum (∅ : Finset (Fin 1)) ell := hell ∅
  simp [L] at hEmpty

end Omega.POM
