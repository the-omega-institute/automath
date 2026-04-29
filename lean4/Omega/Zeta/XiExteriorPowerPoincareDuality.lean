import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Paper label: `cor:xi-exterior-power-poincare-duality`. -/
theorem paper_xi_exterior_power_poincare_duality (q k : ℕ) (hk : k ≤ q + 1)
    (S : Finset ℕ) (hS : S ∈ (Finset.range (q + 1)).powersetCard k) :
    ∃ T : Finset ℕ, T ∈ (Finset.range (q + 1)).powersetCard k ∧
      Finset.sum S (fun i => i) + Finset.sum T (fun i => i) = k * q := by
  classical
  let T : Finset ℕ := S.image fun i => q - i
  have hS' := Finset.mem_powersetCard.mp hS
  have hS_subset : S ⊆ Finset.range (q + 1) := hS'.1
  have hS_card : S.card = k := hS'.2
  have : S.card ≤ q + 1 := by simpa [hS_card] using hk
  have hinj : Set.InjOn (fun i : ℕ => q - i) ↑S := by
    intro a ha b hb hab
    have haq : a ≤ q := Nat.le_of_lt_succ (Finset.mem_range.mp (hS_subset ha))
    have hbq : b ≤ q := Nat.le_of_lt_succ (Finset.mem_range.mp (hS_subset hb))
    have ha_cancel : q - a + a = q := Nat.sub_add_cancel haq
    have hb_cancel : q - b + b = q := Nat.sub_add_cancel hbq
    have hqa : q - b + a = q := by simpa [hab] using ha_cancel
    have hsame : q - b + a = q - b + b := by rw [hqa, hb_cancel]
    exact Nat.add_left_cancel hsame
  have hT_mem : T ∈ (Finset.range (q + 1)).powersetCard k := by
    rw [Finset.mem_powersetCard]
    constructor
    · intro x hx
      rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
      have hiq : i ≤ q := Nat.le_of_lt_succ (Finset.mem_range.mp (hS_subset hi))
      exact Finset.mem_range.mpr (by omega)
    · change (S.image (fun i => q - i)).card = k
      rw [Finset.card_image_of_injOn hinj, hS_card]
  have hT_sum : Finset.sum T (fun i => i) = k * q - Finset.sum S (fun i => i) := by
    change Finset.sum (S.image (fun i => q - i)) (fun i => i) =
      k * q - Finset.sum S (fun i => i)
    rw [Finset.sum_image hinj, Finset.sum_tsub_distrib]
    · have hconst : Finset.sum S (fun _i => q) = S.card * q := by simp
      rw [hconst, hS_card]
    · intro i hi
      exact Nat.le_of_lt_succ (Finset.mem_range.mp (hS_subset hi))
  have hsum_le : Finset.sum S (fun i => i) ≤ k * q := by
    calc
      Finset.sum S (fun i => i) ≤ Finset.sum S (fun _i => q) := by
        exact Finset.sum_le_sum fun i hi =>
          Nat.le_of_lt_succ (Finset.mem_range.mp (hS_subset hi))
      _ = S.card * q := by simp
      _ = k * q := by rw [hS_card]
  refine ⟨T, hT_mem, ?_⟩
  rw [hT_sum]
  exact Nat.add_sub_of_le hsum_le

end Omega.Zeta
