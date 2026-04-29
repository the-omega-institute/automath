import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `prop:pom-resonance-perron-negative-root-field-coprime-q9-13`. -/
theorem paper_pom_resonance_perron_negative_root_field_coprime_q9_13
    (d : ℕ) (hd : 3 ≤ d) (i j : Fin d) (hij : i ≠ j) :
    Subgroup.closure
        ((({σ : Equiv.Perm (Fin d) | σ i = i} : Set (Equiv.Perm (Fin d))) ∪
          ({σ : Equiv.Perm (Fin d) | σ j = j} : Set (Equiv.Perm (Fin d))))) = ⊤ ∧
      Nat.factorial d / Nat.factorial (d - 2) = d * (d - 1) := by
  classical
  let H : Subgroup (Equiv.Perm (Fin d)) :=
    Subgroup.closure
      ((({σ : Equiv.Perm (Fin d) | σ i = i} : Set (Equiv.Perm (Fin d))) ∪
        ({σ : Equiv.Perm (Fin d) | σ j = j} : Set (Equiv.Perm (Fin d)))))
  have h_two : 2 ≤ d := by omega
  have h_three : 2 < d := by omega
  rcases Fin.exists_ne_and_ne_of_two_lt i j h_three with ⟨k, hki, hkj⟩
  have h_swap_fix_i {a b : Fin d} (ha : a ≠ i) (hb : b ≠ i) :
      Equiv.swap a b ∈ H := by
    exact Subgroup.subset_closure (Set.mem_union_left _ (show Equiv.swap a b i = i by
      exact Equiv.swap_apply_of_ne_of_ne ha.symm hb.symm))
  have h_swap_fix_j {a b : Fin d} (ha : a ≠ j) (hb : b ≠ j) :
      Equiv.swap a b ∈ H := by
    exact Subgroup.subset_closure (Set.mem_union_right _ (show Equiv.swap a b j = j by
      exact Equiv.swap_apply_of_ne_of_ne ha.symm hb.symm))
  have h_star : ∀ a : Fin d, Equiv.swap i a ∈ H := by
    intro a
    by_cases hai : a = i
    · subst a
      rw [Equiv.swap_self]
      exact H.one_mem
    · by_cases haj : a = j
      · subst a
        have hk_i : k ≠ i := hki
        have hk_j : k ≠ j := hkj
        have h_left : Equiv.swap k j ∈ H := h_swap_fix_i hk_i hij.symm
        have h_mid : Equiv.swap i k ∈ H := h_swap_fix_j hij hk_j
        have h_prod : Equiv.swap k j * Equiv.swap i k * Equiv.swap k j ∈ H :=
          H.mul_mem (H.mul_mem h_left h_mid) h_left
        have h_eq :
            Equiv.swap k j * Equiv.swap i k * Equiv.swap k j = Equiv.swap j i :=
          Equiv.swap_mul_swap_mul_swap (x := i) (y := k) (z := j) hki.symm hij
        rw [h_eq] at h_prod
        simpa [Equiv.swap_comm] using h_prod
      · exact h_swap_fix_j hij haj
  have h_all_swaps : ∀ a b : Fin d, Equiv.swap a b ∈ H := by
    intro a b
    by_cases ha : a = i
    · subst a
      exact h_star b
    · by_cases hb : b = i
      · subst b
        simpa [Equiv.swap_comm] using h_star a
      · exact h_swap_fix_i ha hb
  have h_closure :
      Subgroup.closure
          ((({σ : Equiv.Perm (Fin d) | σ i = i} : Set (Equiv.Perm (Fin d))) ∪
            ({σ : Equiv.Perm (Fin d) | σ j = j} : Set (Equiv.Perm (Fin d))))) = ⊤ := by
    change H = ⊤
    have hgen : Subgroup.closure {σ : Equiv.Perm (Fin d) | σ.IsSwap} ≤ H :=
      (Subgroup.closure_le H).2 fun σ hσ => by
        rcases hσ with ⟨a, b, hab, rfl⟩
        exact h_all_swaps a b
    rw [Equiv.Perm.closure_isSwap] at hgen
    exact le_antisymm le_top hgen
  have h_factorial :
      Nat.factorial d / Nat.factorial (d - 2) = d * (d - 1) := by
    rw [← Nat.descFactorial_eq_div h_two]
    simp [Nat.descFactorial, Nat.mul_comm]
  exact ⟨h_closure, h_factorial⟩

end Omega.POM
