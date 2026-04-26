import Mathlib
import Omega.POM.MicrocanonicalFoldEntropy
import Omega.POM.MicrocanonicalFoldPosteriorCountAndProb

namespace Omega.POM

open scoped BigOperators

/-- Uniform microcanonical mass of a finite subset. -/
def pom_microcanonical_fold_singleton_and_low_complexity_rarity_uniform_mass
    {α : Type*} [Fintype α] (s : Finset α) : ℚ :=
  (s.card : ℚ) / (Fintype.card α : ℚ)

/-- Union of a finite family of finite subsets. -/
def pom_microcanonical_fold_singleton_and_low_complexity_rarity_family_union
    {α : Type*} [DecidableEq α] (C : Finset (Finset α)) : Finset α :=
  C.biUnion id

/-- A concrete prefix-code envelope for a low-complexity class of binary descriptions. -/
def pom_microcanonical_fold_singleton_and_low_complexity_rarity_complexity_envelope
    (b : ℕ) : ℕ :=
  2 ^ b

/-- Concrete finite-counting package for singleton rarity and finite union bounds in the
microcanonical fold model. -/
def pom_microcanonical_fold_singleton_and_low_complexity_rarity_statement : Prop :=
  (∀ {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] (a : α),
    pom_microcanonical_fold_singleton_and_low_complexity_rarity_uniform_mass ({a} : Finset α) =
      1 / (Fintype.card α : ℚ)) ∧
    (∀ {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] (s : Finset α),
      pom_microcanonical_fold_singleton_and_low_complexity_rarity_uniform_mass s =
        Finset.sum s fun a =>
          pom_microcanonical_fold_singleton_and_low_complexity_rarity_uniform_mass
            ({a} : Finset α)) ∧
    (∀ {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
        (C : Finset (Finset α)),
      pom_microcanonical_fold_singleton_and_low_complexity_rarity_uniform_mass
          (pom_microcanonical_fold_singleton_and_low_complexity_rarity_family_union C) ≤
        Finset.sum C fun s =>
          pom_microcanonical_fold_singleton_and_low_complexity_rarity_uniform_mass s) ∧
    (∀ b n : ℕ, b ≤ n →
      pom_microcanonical_fold_singleton_and_low_complexity_rarity_complexity_envelope b ≤
        pom_microcanonical_fold_singleton_and_low_complexity_rarity_complexity_envelope n)

private lemma pom_microcanonical_fold_singleton_and_low_complexity_rarity_card_pos
    (α : Type*) [Fintype α] [Nonempty α] :
    0 < (Fintype.card α : ℚ) := by
  exact_mod_cast Fintype.card_pos

/-- Paper label: `cor:pom-microcanonical-fold-singleton-and-low-complexity-rarity`. -/
theorem paper_pom_microcanonical_fold_singleton_and_low_complexity_rarity :
    pom_microcanonical_fold_singleton_and_low_complexity_rarity_statement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro α _ _ _ a
    simp [pom_microcanonical_fold_singleton_and_low_complexity_rarity_uniform_mass]
  · intro α _ _ _ s
    calc
      pom_microcanonical_fold_singleton_and_low_complexity_rarity_uniform_mass s =
          (s.card : ℚ) / (Fintype.card α : ℚ) := rfl
      _ = (Finset.sum s fun _ => (1 : ℚ)) / (Fintype.card α : ℚ) := by simp
      _ = Finset.sum s (fun a => (1 : ℚ) / (Fintype.card α : ℚ)) := by
        rw [Finset.sum_div]
      _ =
          Finset.sum s fun a =>
            pom_microcanonical_fold_singleton_and_low_complexity_rarity_uniform_mass
              ({a} : Finset α) := by
        apply Finset.sum_congr rfl
        intro a ha
        simp [pom_microcanonical_fold_singleton_and_low_complexity_rarity_uniform_mass]
  · intro α _ _ _ C
    have hden_pos :
        0 < (Fintype.card α : ℚ) :=
      pom_microcanonical_fold_singleton_and_low_complexity_rarity_card_pos α
    have hcard :
        (pom_microcanonical_fold_singleton_and_low_complexity_rarity_family_union C).card ≤
          Finset.sum C fun s => s.card := by
      simpa [pom_microcanonical_fold_singleton_and_low_complexity_rarity_family_union] using
        (Finset.card_biUnion_le :
          (C.biUnion id).card ≤ Finset.sum C fun s => (id s).card)
    have hcard_rat :
        ((pom_microcanonical_fold_singleton_and_low_complexity_rarity_family_union C).card : ℚ) ≤
          ((Finset.sum C fun s => s.card : ℕ) : ℚ) := by
      exact_mod_cast hcard
    calc
      pom_microcanonical_fold_singleton_and_low_complexity_rarity_uniform_mass
          (pom_microcanonical_fold_singleton_and_low_complexity_rarity_family_union C)
          =
        ((pom_microcanonical_fold_singleton_and_low_complexity_rarity_family_union C).card : ℚ) /
          (Fintype.card α : ℚ) := rfl
      _ ≤ ((Finset.sum C fun s => s.card : ℕ) : ℚ) / (Fintype.card α : ℚ) := by
        exact div_le_div_of_nonneg_right hcard_rat (le_of_lt hden_pos)
      _ =
        Finset.sum C fun s =>
          pom_microcanonical_fold_singleton_and_low_complexity_rarity_uniform_mass s := by
        rw [Nat.cast_sum, Finset.sum_div]
        rfl
  · intro b n hbn
    exact Nat.pow_le_pow_right (by norm_num : 0 < 2) hbn

end Omega.POM
