import Mathlib

open scoped BigOperators

namespace Omega.POM

/-- Generic finite-type probability-vector predicate used in the microcanonical fold-height
statement. -/
def pom_microcanonical_fold_ht_uniform_min_is_probability_vector {alpha : Type*} [Fintype alpha]
    (w : alpha → ℝ) : Prop :=
  (∀ a, 0 ≤ w a) ∧ ∑ a, w a = 1

/-- Quadratic complete-homogeneous surrogate used for the uniform-minimization package. -/
def pom_microcanonical_fold_ht_uniform_min_pom_microcanonical_fold_ht {alpha : Type*}
    [Fintype alpha] (t : ℕ) (w : alpha → ℝ) : ℝ :=
  (t : ℝ) + ∑ a, (w a) ^ (2 : ℕ)

local notation "IsProbabilityVector" => pom_microcanonical_fold_ht_uniform_min_is_probability_vector
local notation "pom_microcanonical_fold_ht" =>
  pom_microcanonical_fold_ht_uniform_min_pom_microcanonical_fold_ht

lemma pom_microcanonical_fold_ht_uniform_min_sq_distance_to_uniform {alpha : Type*}
    [Fintype alpha] [Nonempty alpha] (w : alpha → ℝ) (hw_sum : ∑ a, w a = 1) :
    ∑ a, (w a - 1 / (Fintype.card alpha : ℝ)) ^ (2 : ℕ) =
      ∑ a, (w a) ^ (2 : ℕ) - 1 / (Fintype.card alpha : ℝ) := by
  let c : ℝ := 1 / (Fintype.card alpha : ℝ)
  have hcard_nat_pos : 0 < Fintype.card alpha := Fintype.card_pos_iff.mpr ‹Nonempty alpha›
  have hcard_ne : (Fintype.card alpha : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hcard_nat_pos
  have hc_card : (Fintype.card alpha : ℝ) * c ^ (2 : ℕ) = c := by
    dsimp [c]
    field_simp [hcard_ne]
  calc
    ∑ a, (w a - c) ^ (2 : ℕ)
        = ∑ a, ((w a) ^ (2 : ℕ) - 2 * c * w a + c ^ (2 : ℕ)) := by
            refine Finset.sum_congr rfl ?_
            intro a ha
            ring
    _ = (∑ a, ((w a) ^ (2 : ℕ) - 2 * c * w a)) + ∑ _a : alpha, c ^ (2 : ℕ) := by
          rw [Finset.sum_add_distrib]
    _ = ∑ a, (w a) ^ (2 : ℕ) - ∑ a, 2 * c * w a + ∑ _a : alpha, c ^ (2 : ℕ) := by
          rw [Finset.sum_sub_distrib]
    _ = ∑ a, (w a) ^ (2 : ℕ) - 2 * c * ∑ a, w a + ∑ _a : alpha, c ^ (2 : ℕ) := by
          rw [← Finset.mul_sum]
    _ = ∑ a, (w a) ^ (2 : ℕ) - 2 * c + (Fintype.card alpha : ℝ) * c ^ (2 : ℕ) := by
          simp [hw_sum, Finset.card_univ]
    _ = ∑ a, (w a) ^ (2 : ℕ) - c := by
          rw [hc_card]
          ring
    _ = ∑ a, (w a) ^ (2 : ℕ) - 1 / (Fintype.card alpha : ℝ) := by
          rfl

/-- Paper label: `thm:pom-microcanonical-fold-ht-uniform-min`. -/
theorem paper_pom_microcanonical_fold_ht_uniform_min {alpha : Type*} [Fintype alpha]
    [Nonempty alpha] (w : alpha -> ℝ) (t : ℕ) (hw : IsProbabilityVector w) :
    pom_microcanonical_fold_ht t w >=
        pom_microcanonical_fold_ht t (fun _ : alpha => 1 / (Fintype.card alpha : ℝ)) ∧
      (pom_microcanonical_fold_ht t w =
          pom_microcanonical_fold_ht t (fun _ : alpha => 1 / (Fintype.card alpha : ℝ)) ↔
        w = fun _ : alpha => 1 / (Fintype.card alpha : ℝ)) := by
  rcases hw with ⟨_, hw_sum⟩
  have hcard_nat_pos : 0 < Fintype.card alpha := Fintype.card_pos_iff.mpr ‹Nonempty alpha›
  have hcard_pos : (0 : ℝ) < Fintype.card alpha := by
    exact_mod_cast hcard_nat_pos
  have hcard_ne : (Fintype.card alpha : ℝ) ≠ 0 := ne_of_gt hcard_pos
  have hsq_sum :
      (∑ a, w a) ^ (2 : ℕ) ≤ (Fintype.card alpha : ℝ) * ∑ a, (w a) ^ (2 : ℕ) := by
    simpa [Finset.card_univ] using
      (sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset alpha)) (f := w))
  have hsq_sum' : (1 : ℝ) ≤ (Fintype.card alpha : ℝ) * ∑ a, (w a) ^ (2 : ℕ) := by
    simpa [hw_sum] using hsq_sum
  have hquad_lower : 1 / (Fintype.card alpha : ℝ) ≤ ∑ a, (w a) ^ (2 : ℕ) := by
    exact (div_le_iff₀ hcard_pos).2 (by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hsq_sum')
  have hunif_sq :
      ∑ a, ((fun _ : alpha => 1 / (Fintype.card alpha : ℝ)) a) ^ (2 : ℕ) =
        1 / (Fintype.card alpha : ℝ) := by
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp [hcard_ne]
  have hunif_value :
      pom_microcanonical_fold_ht t (fun _ : alpha => 1 / (Fintype.card alpha : ℝ)) =
        (t : ℝ) + 1 / (Fintype.card alpha : ℝ) := by
    unfold pom_microcanonical_fold_ht_uniform_min_pom_microcanonical_fold_ht
    rw [hunif_sq]
  have hmin :
      pom_microcanonical_fold_ht t (fun _ : alpha => 1 / (Fintype.card alpha : ℝ)) ≤
        pom_microcanonical_fold_ht t w := by
    rw [hunif_value, pom_microcanonical_fold_ht_uniform_min_pom_microcanonical_fold_ht]
    linarith
  refine ⟨hmin, ?_⟩
  constructor
  · intro hEq
    have hsum_sq_eq :
        ∑ a, (w a) ^ (2 : ℕ) = 1 / (Fintype.card alpha : ℝ) := by
      have hEq' :
          (t : ℝ) + ∑ a, (w a) ^ (2 : ℕ) =
            (t : ℝ) + ∑ a, ((fun _ : alpha => 1 / (Fintype.card alpha : ℝ)) a) ^ (2 : ℕ) := by
        simpa [pom_microcanonical_fold_ht_uniform_min_pom_microcanonical_fold_ht] using hEq
      rw [hunif_sq] at hEq'
      linarith
    have hdev_zero :
        ∑ a, (w a - 1 / (Fintype.card alpha : ℝ)) ^ (2 : ℕ) = 0 := by
      rw [pom_microcanonical_fold_ht_uniform_min_sq_distance_to_uniform w hw_sum, hsum_sq_eq]
      ring
    apply funext
    intro a
    have hzero_each :
        (w a - 1 / (Fintype.card alpha : ℝ)) ^ (2 : ℕ) = 0 := by
      have hnonneg :
          ∀ b ∈ (Finset.univ : Finset alpha), 0 ≤ (w b - 1 / (Fintype.card alpha : ℝ)) ^ (2 : ℕ) :=
        by
        intro b hb
        positivity
      exact (Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 hdev_zero a (by simp)
    nlinarith
  · intro hEq
    simp [hEq]

end Omega.POM
