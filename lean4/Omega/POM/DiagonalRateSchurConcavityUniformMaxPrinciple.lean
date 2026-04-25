import Omega.POM.DiagonalRateStrictSchurConcavity
import Omega.POM.DiagonalRateUniformGlobalMax

open scoped BigOperators

namespace Omega.POM

/-- Concrete data for the uniform-maximizer package of the diagonal-rate functional. -/
structure pom_diagonal_rate_schur_concavity_uniform_max_principle_data where
  n : ℕ
  δ : ℝ
  w : Fin n → ℝ
  hn : 2 ≤ n
  hδ0 : 0 < δ
  hδ1 : δ < 1
  hw : IsProbabilityVector w
  pom_diagonal_rate_schur_concavity_uniform_max_principle_not_uniform :
    ¬ ∀ i : Fin n, w i = (1 : ℝ) / n
  pom_diagonal_rate_schur_concavity_uniform_max_principle_strict_active_interval :
    (¬ ∀ i : Fin n, w i = (1 : ℝ) / n) →
      ∑ _ : Fin n, ((1 : ℝ) / n) ^ (2 : ℕ) < ∑ i : Fin n, (w i) ^ (2 : ℕ)

namespace pom_diagonal_rate_schur_concavity_uniform_max_principle_data

/-- The uniform reference profile on `Fin n`. -/
noncomputable def pom_diagonal_rate_schur_concavity_uniform_max_principle_uniform
    (h : pom_diagonal_rate_schur_concavity_uniform_max_principle_data) : Fin h.n → ℝ :=
  fun _ => (1 : ℝ) / h.n

/-- Paper-facing statement: the diagonal rate is maximized at the uniform profile, and on the
active interval the inequality is strict away from the uniform orbit. -/
def statement (h : pom_diagonal_rate_schur_concavity_uniform_max_principle_data) : Prop :=
  pomDiagonalRate h.w h.δ <=
      pomDiagonalRate h.pom_diagonal_rate_schur_concavity_uniform_max_principle_uniform h.δ ∧
    ((¬ ∀ i : Fin h.n, h.w i = (1 : ℝ) / h.n) →
      pomDiagonalRate h.w h.δ <
        pomDiagonalRate h.pom_diagonal_rate_schur_concavity_uniform_max_principle_uniform h.δ)

end pom_diagonal_rate_schur_concavity_uniform_max_principle_data

open pom_diagonal_rate_schur_concavity_uniform_max_principle_data

private lemma pom_diagonal_rate_schur_concavity_uniform_max_principle_uniform_prob
    (h : pom_diagonal_rate_schur_concavity_uniform_max_principle_data) :
    IsProbabilityVector h.pom_diagonal_rate_schur_concavity_uniform_max_principle_uniform := by
  have hn_pos : 0 < h.n := lt_of_lt_of_le (by decide : 0 < 2) h.hn
  have hnR_pos : (0 : ℝ) < h.n := by exact_mod_cast hn_pos
  have hnR_ne : (h.n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn_pos)
  refine ⟨?_, ?_⟩
  · intro i
    exact div_nonneg zero_le_one hnR_pos.le
  · simp [pom_diagonal_rate_schur_concavity_uniform_max_principle_uniform, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, hnR_ne]

private lemma pom_diagonal_rate_schur_concavity_uniform_max_principle_uniform_majorizes
    (h : pom_diagonal_rate_schur_concavity_uniform_max_principle_data) :
    Majorizes h.w h.pom_diagonal_rate_schur_concavity_uniform_max_principle_uniform := by
  rcases h.hw with ⟨_, hw_sum⟩
  have hn_pos : 0 < h.n := lt_of_lt_of_le (by decide : 0 < 2) h.hn
  have hnR_pos : (0 : ℝ) < h.n := by exact_mod_cast hn_pos
  have hnR_ne : (h.n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn_pos)
  have hcs :
      (∑ i : Fin h.n, h.w i) ^ (2 : ℕ) ≤ (h.n : ℝ) * ∑ i : Fin h.n, (h.w i) ^ (2 : ℕ) := by
    simpa [Finset.card_univ] using
      (sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin h.n))) (f := h.w))
  have hquad_mul : (1 : ℝ) ≤ (h.n : ℝ) * ∑ i : Fin h.n, (h.w i) ^ (2 : ℕ) := by
    simpa [hw_sum] using hcs
  have hquad :
      (1 : ℝ) / h.n ≤ ∑ i : Fin h.n, (h.w i) ^ (2 : ℕ) := by
    exact (div_le_iff₀ hnR_pos).2 (by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hquad_mul)
  have hunif_sum :
      ∑ i : Fin h.n,
          h.pom_diagonal_rate_schur_concavity_uniform_max_principle_uniform i =
        1 := by
    simpa using
      (pom_diagonal_rate_schur_concavity_uniform_max_principle_uniform_prob h).2
  have hunif_sq :
      ∑ i : Fin h.n,
          (h.pom_diagonal_rate_schur_concavity_uniform_max_principle_uniform i) ^ (2 : ℕ) =
        (1 : ℝ) / h.n := by
    calc
      ∑ i : Fin h.n,
          (h.pom_diagonal_rate_schur_concavity_uniform_max_principle_uniform i) ^ (2 : ℕ)
          = (h.n : ℝ) * (((1 : ℝ) / h.n) ^ (2 : ℕ)) := by
              simp [pom_diagonal_rate_schur_concavity_uniform_max_principle_uniform,
                Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = (1 : ℝ) / h.n := by
            field_simp [hnR_ne]
  refine ⟨?_, ?_⟩
  · rw [hunif_sum, hw_sum]
  · rw [hunif_sq]
    exact hquad

/-- Paper label: `thm:pom-diagonal-rate-schur-concavity-uniform-max-principle`. -/
theorem paper_pom_diagonal_rate_schur_concavity_uniform_max_principle
    (h : pom_diagonal_rate_schur_concavity_uniform_max_principle_data) : h.statement := by
  have hweak :
      pomDiagonalRate h.w h.δ <=
        pomDiagonalRate h.pom_diagonal_rate_schur_concavity_uniform_max_principle_uniform h.δ := by
    change pomDiagonalRate h.w h.δ <= pomDiagonalRate (fun _ : Fin h.n => (1 : ℝ) / h.n) h.δ
    exact paper_pom_diagonal_rate_uniform_global_max h.δ h.hn h.hδ0.le h.hδ1.le h.hw
  have hunif_prob :
      IsProbabilityVector h.pom_diagonal_rate_schur_concavity_uniform_max_principle_uniform :=
    pom_diagonal_rate_schur_concavity_uniform_max_principle_uniform_prob h
  have hmajor :
      Majorizes h.w h.pom_diagonal_rate_schur_concavity_uniform_max_principle_uniform :=
    pom_diagonal_rate_schur_concavity_uniform_max_principle_uniform_majorizes h
  refine ⟨hweak, ?_⟩
  intro hnot
  have hsq :
      ∑ i : Fin h.n,
          (h.pom_diagonal_rate_schur_concavity_uniform_max_principle_uniform i) ^ (2 : ℕ) <
        ∑ i : Fin h.n, (h.w i) ^ (2 : ℕ) :=
    h.pom_diagonal_rate_schur_concavity_uniform_max_principle_strict_active_interval hnot
  have hstrict := paper_pom_diagonal_rate_strict_schur_concavity h.δ h.hδ0 h.hδ1 hunif_prob h.hw
    hmajor hsq
  simpa [pom_diagonal_rate_schur_concavity_uniform_max_principle_uniform] using hstrict

end Omega.POM
