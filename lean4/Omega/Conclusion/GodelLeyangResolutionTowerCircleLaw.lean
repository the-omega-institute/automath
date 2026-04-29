import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

def conclusion_godel_leyang_resolution_tower_circle_law_factor_root
    (B M k : ℕ) (z : ℂ) : Prop :=
  z ^ ((M + 1) * B ^ k) = 1 ∧ z ^ (B ^ k) ≠ 1

def conclusion_godel_leyang_resolution_tower_circle_law_factor_root_count
    (B M k : ℕ) : ℕ :=
  M * B ^ k

def conclusion_godel_leyang_resolution_tower_circle_law_tower_degree
    (B M n : ℕ) : ℕ :=
  (Finset.range n).sum
    fun k => conclusion_godel_leyang_resolution_tower_circle_law_factor_root_count B M k

def conclusion_godel_leyang_resolution_tower_circle_law_statement : Prop :=
  (∀ B M n k (z : ℂ), 2 ≤ B → 1 ≤ M → k < n →
      conclusion_godel_leyang_resolution_tower_circle_law_factor_root B M k z →
        ‖z‖ = 1) ∧
    (∀ B M n,
      conclusion_godel_leyang_resolution_tower_circle_law_tower_degree B M n =
        (Finset.range n).sum
          fun k => conclusion_godel_leyang_resolution_tower_circle_law_factor_root_count B M k) ∧
    (∀ B M k,
      conclusion_godel_leyang_resolution_tower_circle_law_factor_root_count B M k =
        M * B ^ k)

lemma conclusion_godel_leyang_resolution_tower_circle_law_norm_of_root_of_unity
    {N : ℕ} {z : ℂ} (hN : N ≠ 0) (hz : z ^ N = 1) : ‖z‖ = 1 := by
  have hpow : ‖z‖ ^ N = (1 : ℝ) := by
    rw [← norm_pow, hz, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg z) hN).mp hpow

/-- Paper label: `thm:conclusion-godel-leyang-resolution-tower-circle-law`. -/
theorem paper_conclusion_godel_leyang_resolution_tower_circle_law :
    conclusion_godel_leyang_resolution_tower_circle_law_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro B M n k z hB hM _hk hz
    have hBpos : 0 < B := by omega
    exact conclusion_godel_leyang_resolution_tower_circle_law_norm_of_root_of_unity
      (Nat.ne_of_gt (Nat.mul_pos (Nat.succ_pos M) (Nat.pow_pos hBpos))) hz.1
  · intro B M n
    rfl
  · intro B M k
    rfl

end

end Omega.Conclusion
