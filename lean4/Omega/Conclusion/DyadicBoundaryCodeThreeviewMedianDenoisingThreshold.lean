import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Omega.Conclusion.DyadicBoundaryCodeExactUniqueDecodingRadius

namespace Omega.Conclusion

open scoped BigOperators

/-- Number of the three error supports containing a coordinate. -/
def conclusion_dyadic_boundary_code_threeview_median_denoising_threshold_support_count
    {m : ℕ} (E₁ E₂ E₃ : Finset (Fin m)) (i : Fin m) : ℕ :=
  (if i ∈ E₁ then 1 else 0) + (if i ∈ E₂ then 1 else 0) + (if i ∈ E₃ then 1 else 0)

/-- Majority/median error support: coordinates corrupted in at least two of the three views. -/
def conclusion_dyadic_boundary_code_threeview_median_denoising_threshold_majority_support
    {m : ℕ} (E₁ E₂ E₃ : Finset (Fin m)) : Finset (Fin m) :=
  Finset.univ.filter fun i =>
    2 ≤ conclusion_dyadic_boundary_code_threeview_median_denoising_threshold_support_count
      E₁ E₂ E₃ i

private lemma
    conclusion_dyadic_boundary_code_threeview_median_denoising_threshold_support_count_sum
    {m : ℕ} (E₁ E₂ E₃ : Finset (Fin m)) :
    (Finset.sum Finset.univ fun i : Fin m =>
      conclusion_dyadic_boundary_code_threeview_median_denoising_threshold_support_count
        E₁ E₂ E₃ i) =
      E₁.card + E₂.card + E₃.card := by
  simp [conclusion_dyadic_boundary_code_threeview_median_denoising_threshold_support_count,
    Finset.sum_add_distrib]

private lemma
    conclusion_dyadic_boundary_code_threeview_median_denoising_threshold_majority_card_bound
    {m : ℕ} (E₁ E₂ E₃ : Finset (Fin m)) :
    2 *
        (conclusion_dyadic_boundary_code_threeview_median_denoising_threshold_majority_support
          E₁ E₂ E₃).card ≤
      E₁.card + E₂.card + E₃.card := by
  let M :=
    conclusion_dyadic_boundary_code_threeview_median_denoising_threshold_majority_support
      E₁ E₂ E₃
  let c :=
    conclusion_dyadic_boundary_code_threeview_median_denoising_threshold_support_count
      E₁ E₂ E₃
  have hM : ∀ i ∈ M, 2 ≤ c i := by
    intro i hi
    simpa [M, c,
      conclusion_dyadic_boundary_code_threeview_median_denoising_threshold_majority_support]
      using (Finset.mem_filter.mp hi).2
  have hmajor : 2 * M.card ≤ Finset.sum M (fun i => c i) := by
    calc
      2 * M.card = Finset.sum M (fun _i => 2) := by simp [Nat.mul_comm]
      _ ≤ Finset.sum M (fun i => c i) := Finset.sum_le_sum hM
  have hsubset : M ⊆ (Finset.univ : Finset (Fin m)) := by
    intro i _
    simp
  have hmono : Finset.sum M (fun i => c i) ≤ Finset.sum Finset.univ (fun i : Fin m => c i) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
      intro i _ _
      exact Nat.zero_le (c i))
  calc
    2 * M.card ≤ Finset.sum M (fun i => c i) := hmajor
    _ ≤ Finset.sum Finset.univ (fun i : Fin m => c i) := hmono
    _ = E₁.card + E₂.card + E₃.card := by
      simpa [c] using
        conclusion_dyadic_boundary_code_threeview_median_denoising_threshold_support_count_sum
          E₁ E₂ E₃

/-- Concrete three-view denoising statement: majority support loses at most `⌊3r/2⌋` coordinates,
and under the threshold this lies within the exact unique-decoding radius `n - 1`. -/
def conclusion_dyadic_boundary_code_threeview_median_denoising_threshold_statement
    (m n r : ℕ) : Prop :=
  (∀ E₁ E₂ E₃ : Finset (Fin m),
      E₁.card ≤ r → E₂.card ≤ r → E₃.card ≤ r →
        2 *
            (conclusion_dyadic_boundary_code_threeview_median_denoising_threshold_majority_support
              E₁ E₂ E₃).card ≤
          E₁.card + E₂.card + E₃.card ∧
        (conclusion_dyadic_boundary_code_threeview_median_denoising_threshold_majority_support
            E₁ E₂ E₃).card ≤ (3 * r) / 2 ∧
        (r ≤ (2 * n - 2) / 3 →
          (conclusion_dyadic_boundary_code_threeview_median_denoising_threshold_majority_support
            E₁ E₂ E₃).card ≤ n - 1)) ∧
    (1 ≤ n → dyadicBoundaryCodeUniqueDecodingRadius m n = n - 1)

/-- Paper label:
`cor:conclusion-dyadic-boundary-code-threeview-median-denoising-threshold`. -/
theorem paper_conclusion_dyadic_boundary_code_threeview_median_denoising_threshold
    (m n r : ℕ) :
    conclusion_dyadic_boundary_code_threeview_median_denoising_threshold_statement m n r := by
  refine ⟨?_, ?_⟩
  · intro E₁ E₂ E₃ hE₁ hE₂ hE₃
    let M :=
      conclusion_dyadic_boundary_code_threeview_median_denoising_threshold_majority_support
        E₁ E₂ E₃
    have hcount :
        2 * M.card ≤ E₁.card + E₂.card + E₃.card :=
      conclusion_dyadic_boundary_code_threeview_median_denoising_threshold_majority_card_bound
        E₁ E₂ E₃
    have hsum : E₁.card + E₂.card + E₃.card ≤ 3 * r := by omega
    have htwice : 2 * M.card ≤ 3 * r := le_trans hcount hsum
    have hfloor : M.card ≤ (3 * r) / 2 := by
      rw [Nat.le_div_iff_mul_le (by decide : 0 < 2)]
      simpa [Nat.mul_comm] using htwice
    refine ⟨by simpa [M] using hcount, by simpa [M] using hfloor, ?_⟩
    intro hthreshold
    have hthreshold' : r * 3 ≤ 2 * n - 2 :=
      (Nat.le_div_iff_mul_le (by decide : 0 < 3)).mp hthreshold
    have htwiceRadius : M.card * 2 ≤ 2 * (n - 1) := by
      have : M.card * 2 ≤ 3 * r := by simpa [Nat.mul_comm] using htwice
      omega
    have hradius : M.card ≤ n - 1 := by omega
    simpa [M] using hradius
  · intro hn
    exact (paper_conclusion_dyadic_boundary_code_exact_unique_decoding_radius m n hn).2.1

end Omega.Conclusion
