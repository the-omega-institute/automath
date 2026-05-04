import Mathlib.Combinatorics.Derangements.Finite
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

namespace Omega.Folding

open Equiv Fintype Function

/-- The derangement-count helper for the `S₁₉` rencontres fixed-point density statement. -/
def fold_gauge_anomaly_h_rencontres_fixed_point_density_derangements (n : ℕ) : ℕ :=
  numDerangements n

/-- Inclusion-exclusion formula for the prefixed derangement-count helper. -/
theorem fold_gauge_anomaly_h_rencontres_fixed_point_density_derangements_inclusion_exclusion
    (n : ℕ) :
    (fold_gauge_anomaly_h_rencontres_fixed_point_density_derangements n : ℤ) =
      ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * Nat.ascFactorial (k + 1) (n - k) := by
  simpa [fold_gauge_anomaly_h_rencontres_fixed_point_density_derangements] using
    (numDerangements_sum n)

/-- Fixed-point set of a permutation in the `S₁₉` rencontres count. -/
def fold_gauge_anomaly_h_rencontres_fixed_point_density_fixedSet
    (σ : Equiv.Perm (Fin 19)) : Finset (Fin 19) :=
  Finset.univ.filter fun i => σ i = i

/-- For a chosen fixed-point set, permutations with exactly that fixed set are derangements on
the complement. -/
noncomputable def fold_gauge_anomaly_h_rencontres_fixed_point_density_fixed_set_equiv
    (s : Finset (Fin 19)) :
    {σ : Equiv.Perm (Fin 19) //
        fold_gauge_anomaly_h_rencontres_fixed_point_density_fixedSet σ = s} ≃
      derangements ({i : Fin 19 // i ∉ s}) :=
  ((derangements.subtypeEquiv (fun i : Fin 19 => i ∉ s)).trans
      (subtypeEquivRight fun σ => by
        constructor
        · intro h
          ext i
          have hi : (σ i = i) ↔ i ∈ s := by
            simpa [mem_fixedPoints_iff] using (h i).symm
          simpa [fold_gauge_anomaly_h_rencontres_fixed_point_density_fixedSet] using hi
        · intro h i
          have hi : i ∈ fixedPoints σ ↔ i ∈ s := by
            rw [← h]
            simp [fold_gauge_anomaly_h_rencontres_fixed_point_density_fixedSet,
              Function.fixedPoints, Function.IsFixedPt]
          simpa using hi.symm)).symm

/-- Split permutations with `r` fixed points by first choosing the fixed-point set. -/
noncomputable def fold_gauge_anomaly_h_rencontres_fixed_point_density_fixed_count_equiv
    (r : ℕ) :
    {σ : Equiv.Perm (Fin 19) //
        (fold_gauge_anomaly_h_rencontres_fixed_point_density_fixedSet σ).card = r} ≃
      Σ s : {s : Finset (Fin 19) // s.card = r},
        derangements ({i : Fin 19 // i ∉ s.1}) :=
  ({
      toFun := fun σ =>
        ⟨⟨fold_gauge_anomaly_h_rencontres_fixed_point_density_fixedSet σ.1, σ.2⟩,
          ⟨σ.1, rfl⟩⟩
      invFun := fun s => ⟨s.2.1, by rw [s.2.2]; exact s.1.2⟩
      left_inv := fun σ => by
        rcases σ with ⟨σ, hσ⟩
        apply Subtype.ext
        change σ = σ
        rfl
      right_inv := fun s => by
        rcases s with ⟨⟨s, hs⟩, ⟨σ, hσ⟩⟩
        cases hσ
        rfl } :
      {σ : Equiv.Perm (Fin 19) //
        (fold_gauge_anomaly_h_rencontres_fixed_point_density_fixedSet σ).card = r} ≃
      Σ s : {s : Finset (Fin 19) // s.card = r},
        {σ : Equiv.Perm (Fin 19) //
          fold_gauge_anomaly_h_rencontres_fixed_point_density_fixedSet σ = s.1}).trans
    (Equiv.sigmaCongrRight fun s =>
      fold_gauge_anomaly_h_rencontres_fixed_point_density_fixed_set_equiv s.1)

theorem paper_fold_gauge_anomaly_h_rencontres_fixed_point_density (r : ℕ) (hr : r ≤ 19) :
    Fintype.card {σ : Equiv.Perm (Fin 19) //
      (Finset.univ.filter (fun i => σ i = i)).card = r} =
        Nat.choose 19 r *
          fold_gauge_anomaly_h_rencontres_fixed_point_density_derangements (19 - r) := by
  classical
  have hround_guard : r ≤ 19 := hr
  clear hround_guard
  change Fintype.card {σ : Equiv.Perm (Fin 19) //
      (fold_gauge_anomaly_h_rencontres_fixed_point_density_fixedSet σ).card = r} =
        Nat.choose 19 r *
          fold_gauge_anomaly_h_rencontres_fixed_point_density_derangements (19 - r)
  rw [Fintype.card_congr
    (fold_gauge_anomaly_h_rencontres_fixed_point_density_fixed_count_equiv r)]
  rw [Fintype.card_sigma]
  have hfiber :
      ∀ s : {s : Finset (Fin 19) // s.card = r},
        Fintype.card (derangements ({i : Fin 19 // i ∉ s.1})) =
          fold_gauge_anomaly_h_rencontres_fixed_point_density_derangements (19 - r) := by
    intro s
    rw [fold_gauge_anomaly_h_rencontres_fixed_point_density_derangements,
      card_derangements_eq_numDerangements]
    congr 1
    rw [Fintype.card_subtype]
    have hfilter :
        (Finset.univ.filter fun i : Fin 19 => i ∉ s.1) = s.1ᶜ := by
      ext i
      simp
    rw [hfilter, Finset.card_compl, Fintype.card_fin, s.2]
  simp_rw [hfiber]
  simp [Fintype.card_finset_len, Fintype.card_fin]

end Omega.Folding
