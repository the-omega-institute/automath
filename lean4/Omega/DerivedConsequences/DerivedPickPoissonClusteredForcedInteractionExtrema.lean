import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace Omega.DerivedConsequences

open scoped BigOperators

/-- The clustered forced-interaction term written in the square-sum form
`κ² - ∑ κ_r²`. -/
def derived_pick_poisson_clustered_forced_interaction_extrema_interaction {R : ℕ}
    (derived_pick_poisson_clustered_forced_interaction_extrema_kappaParts : Fin R → ℤ) : ℤ :=
  (∑ r, derived_pick_poisson_clustered_forced_interaction_extrema_kappaParts r) ^ 2 -
    ∑ r, derived_pick_poisson_clustered_forced_interaction_extrema_kappaParts r ^ 2

/-- Concrete integer-envelope statement for the clustered forced-interaction term. -/
def derived_pick_poisson_clustered_forced_interaction_extrema_statement : Prop :=
  ∀ κ R : ℕ, 1 ≤ R → R ≤ κ →
    let q := κ / R
    let s := κ % R
    ∀ derived_pick_poisson_clustered_forced_interaction_extrema_kappaParts : Fin R → ℤ,
      (∀ r, 1 ≤ derived_pick_poisson_clustered_forced_interaction_extrema_kappaParts r) →
      (∑ r, derived_pick_poisson_clustered_forced_interaction_extrema_kappaParts r) = (κ : ℤ) →
      ((R - 1) * (2 * κ - R) : ℤ) ≤
          derived_pick_poisson_clustered_forced_interaction_extrema_interaction
            derived_pick_poisson_clustered_forced_interaction_extrema_kappaParts ∧
        derived_pick_poisson_clustered_forced_interaction_extrema_interaction
            derived_pick_poisson_clustered_forced_interaction_extrema_kappaParts ≤
          (κ : ℤ) ^ 2 - (((R : ℤ) - s) * (q : ℤ) ^ 2 + s * ((q : ℤ) + 1) ^ 2)

theorem paper_derived_pick_poisson_clustered_forced_interaction_extrema :
    derived_pick_poisson_clustered_forced_interaction_extrema_statement := by
  intro κ R hR hRkappa q s
  intro derived_pick_poisson_clustered_forced_interaction_extrema_kappaParts
  intro hpos hsum
  dsimp [q, s]
  let derived_pick_poisson_clustered_forced_interaction_extrema_excess : Fin R → ℤ :=
    fun r => derived_pick_poisson_clustered_forced_interaction_extrema_kappaParts r - 1
  have derived_pick_poisson_clustered_forced_interaction_extrema_excess_nonneg :
      ∀ r, 0 ≤ derived_pick_poisson_clustered_forced_interaction_extrema_excess r := by
    intro r
    dsimp [derived_pick_poisson_clustered_forced_interaction_extrema_excess]
    linarith [hpos r]
  have derived_pick_poisson_clustered_forced_interaction_extrema_excess_sum :
      (∑ r, derived_pick_poisson_clustered_forced_interaction_extrema_excess r) =
        (κ - R : ℤ) := by
    dsimp [derived_pick_poisson_clustered_forced_interaction_extrema_excess]
    rw [Finset.sum_sub_distrib, hsum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    norm_num
  have derived_pick_poisson_clustered_forced_interaction_extrema_excess_sq_le :
      (∑ r, derived_pick_poisson_clustered_forced_interaction_extrema_excess r ^ 2) ≤
        (∑ r, derived_pick_poisson_clustered_forced_interaction_extrema_excess r) ^ 2 := by
    exact Finset.sum_sq_le_sq_sum_of_nonneg fun r _ =>
      derived_pick_poisson_clustered_forced_interaction_extrema_excess_nonneg r
  have derived_pick_poisson_clustered_forced_interaction_extrema_parts_sq_le :
      (∑ r, derived_pick_poisson_clustered_forced_interaction_extrema_kappaParts r ^ 2) ≤
        ((κ - R : ℤ) ^ 2 + 2 * (κ - R : ℤ) + R) := by
    calc
      (∑ r, derived_pick_poisson_clustered_forced_interaction_extrema_kappaParts r ^ 2)
          = ∑ r, (derived_pick_poisson_clustered_forced_interaction_extrema_excess r + 1) ^ 2 := by
              congr with r
              dsimp [derived_pick_poisson_clustered_forced_interaction_extrema_excess]
              ring
      _ = ∑ r,
            (derived_pick_poisson_clustered_forced_interaction_extrema_excess r ^ 2 +
              (2 * derived_pick_poisson_clustered_forced_interaction_extrema_excess r + 1)) := by
              congr with r
              ring
      _ = (∑ r, derived_pick_poisson_clustered_forced_interaction_extrema_excess r ^ 2) +
            (2 * ∑ r, derived_pick_poisson_clustered_forced_interaction_extrema_excess r + R) := by
              simp [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const,
                Finset.card_univ, add_assoc, add_comm]
      _ ≤ (∑ r, derived_pick_poisson_clustered_forced_interaction_extrema_excess r) ^ 2 +
            (2 * ∑ r, derived_pick_poisson_clustered_forced_interaction_extrema_excess r + R) := by
              gcongr
      _ = ((κ - R : ℤ) ^ 2 + 2 * (κ - R : ℤ) + R) := by
              rw [derived_pick_poisson_clustered_forced_interaction_extrema_excess_sum]
              ring
  have derived_pick_poisson_clustered_forced_interaction_extrema_lower :
      ((R - 1) * (2 * κ - R) : ℤ) ≤
        derived_pick_poisson_clustered_forced_interaction_extrema_interaction
          derived_pick_poisson_clustered_forced_interaction_extrema_kappaParts := by
    have hsum_sq :
        ((∑ r, derived_pick_poisson_clustered_forced_interaction_extrema_kappaParts r) ^ 2 : ℤ) =
          (κ : ℤ) ^ 2 := by
      rw [hsum]
    unfold derived_pick_poisson_clustered_forced_interaction_extrema_interaction
    rw [hsum_sq]
    have hsub :=
      sub_le_sub_left derived_pick_poisson_clustered_forced_interaction_extrema_parts_sq_le
        ((κ : ℤ) ^ 2)
    nlinarith [hsub]
  let derived_pick_poisson_clustered_forced_interaction_extrema_qz : ℤ := κ / R
  let derived_pick_poisson_clustered_forced_interaction_extrema_delta : Fin R → ℤ :=
    fun r => derived_pick_poisson_clustered_forced_interaction_extrema_kappaParts r -
      derived_pick_poisson_clustered_forced_interaction_extrema_qz
  have derived_pick_poisson_clustered_forced_interaction_extrema_delta_sq_ge :
      ∀ r, derived_pick_poisson_clustered_forced_interaction_extrema_delta r ≤
        derived_pick_poisson_clustered_forced_interaction_extrema_delta r ^ 2 := by
    intro r
    dsimp [derived_pick_poisson_clustered_forced_interaction_extrema_delta]
    nlinarith
  have derived_pick_poisson_clustered_forced_interaction_extrema_delta_sum :
      (∑ r, derived_pick_poisson_clustered_forced_interaction_extrema_delta r) = (κ % R : ℤ) := by
    dsimp [derived_pick_poisson_clustered_forced_interaction_extrema_delta,
      derived_pick_poisson_clustered_forced_interaction_extrema_qz]
    rw [Finset.sum_sub_distrib, hsum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hdivmod : (κ : ℤ) - (R : ℤ) * (κ / R : ℤ) = (κ % R : ℤ) := by
      have hmodadd_nat : κ % R + R * (κ / R) = κ := Nat.mod_add_div κ R
      have hmodadd : (κ % R : ℤ) + (R : ℤ) * (κ / R : ℤ) = (κ : ℤ) := by
        exact_mod_cast hmodadd_nat
      linarith
    simpa using hdivmod
  have derived_pick_poisson_clustered_forced_interaction_extrema_delta_sq_ge_sum :
      (κ % R : ℤ) ≤
        ∑ r, derived_pick_poisson_clustered_forced_interaction_extrema_delta r ^ 2 := by
    have hsum_le :
        (∑ r, derived_pick_poisson_clustered_forced_interaction_extrema_delta r) ≤
          ∑ r, derived_pick_poisson_clustered_forced_interaction_extrema_delta r ^ 2 := by
      exact Finset.sum_le_sum fun r _ =>
        derived_pick_poisson_clustered_forced_interaction_extrema_delta_sq_ge r
    rw [derived_pick_poisson_clustered_forced_interaction_extrema_delta_sum] at hsum_le
    exact hsum_le
  have derived_pick_poisson_clustered_forced_interaction_extrema_parts_sq_ge :
      ((R : ℤ) - (κ % R : ℤ)) * (derived_pick_poisson_clustered_forced_interaction_extrema_qz ^ 2) +
          (κ % R : ℤ) * (derived_pick_poisson_clustered_forced_interaction_extrema_qz + 1) ^ 2 ≤
        ∑ r, derived_pick_poisson_clustered_forced_interaction_extrema_kappaParts r ^ 2 := by
    calc
      ((R : ℤ) - (κ % R : ℤ)) * (derived_pick_poisson_clustered_forced_interaction_extrema_qz ^ 2) +
            (κ % R : ℤ) * (derived_pick_poisson_clustered_forced_interaction_extrema_qz + 1) ^ 2
          = (R : ℤ) * (derived_pick_poisson_clustered_forced_interaction_extrema_qz ^ 2) +
              2 * derived_pick_poisson_clustered_forced_interaction_extrema_qz * (κ % R : ℤ) +
              (κ % R : ℤ) := by
                ring
      _ ≤ (R : ℤ) * (derived_pick_poisson_clustered_forced_interaction_extrema_qz ^ 2) +
            2 * derived_pick_poisson_clustered_forced_interaction_extrema_qz * (κ % R : ℤ) +
            ∑ r, derived_pick_poisson_clustered_forced_interaction_extrema_delta r ^ 2 := by
              gcongr
      _ = (∑ r, derived_pick_poisson_clustered_forced_interaction_extrema_delta r ^ 2) +
            2 * derived_pick_poisson_clustered_forced_interaction_extrema_qz *
              (∑ r, derived_pick_poisson_clustered_forced_interaction_extrema_delta r) +
            (R : ℤ) * (derived_pick_poisson_clustered_forced_interaction_extrema_qz ^ 2) := by
              rw [derived_pick_poisson_clustered_forced_interaction_extrema_delta_sum]
              ring
      _ = ∑ r,
            (derived_pick_poisson_clustered_forced_interaction_extrema_delta r ^ 2 +
              2 * derived_pick_poisson_clustered_forced_interaction_extrema_qz *
                derived_pick_poisson_clustered_forced_interaction_extrema_delta r +
              derived_pick_poisson_clustered_forced_interaction_extrema_qz ^ 2) := by
              simp [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const,
                Finset.card_univ, add_comm]
      _ = ∑ r, derived_pick_poisson_clustered_forced_interaction_extrema_kappaParts r ^ 2 := by
              congr with r
              dsimp [derived_pick_poisson_clustered_forced_interaction_extrema_delta,
                derived_pick_poisson_clustered_forced_interaction_extrema_qz]
              ring
  have derived_pick_poisson_clustered_forced_interaction_extrema_upper :
      derived_pick_poisson_clustered_forced_interaction_extrema_interaction
          derived_pick_poisson_clustered_forced_interaction_extrema_kappaParts ≤
        (κ : ℤ) ^ 2 - (((R : ℤ) - (κ % R : ℤ)) * (κ / R : ℤ) ^ 2 +
          (κ % R : ℤ) * ((κ / R : ℤ) + 1) ^ 2) := by
    have hsum_sq :
        ((∑ r, derived_pick_poisson_clustered_forced_interaction_extrema_kappaParts r) ^ 2 : ℤ) =
          (κ : ℤ) ^ 2 := by
      rw [hsum]
    unfold derived_pick_poisson_clustered_forced_interaction_extrema_interaction
    rw [hsum_sq]
    exact sub_le_sub_left derived_pick_poisson_clustered_forced_interaction_extrema_parts_sq_ge
      ((κ : ℤ) ^ 2)
  exact ⟨derived_pick_poisson_clustered_forced_interaction_extrema_lower,
    derived_pick_poisson_clustered_forced_interaction_extrema_upper⟩

end Omega.DerivedConsequences
