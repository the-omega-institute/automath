import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Omega.Conclusion.SectionLedgerKL

open Real Finset

variable {X : Type*} [Fintype X] [Nonempty X]

/-- Pushforward distribution `π(x) = d(x) / N`.
    thm:conclusion-section-ledger-kl-identity -/
noncomputable def pushforward (d : X → ℕ) (N : ℕ) (x : X) : ℝ :=
  (d x : ℝ) / (N : ℝ)

/-- Uniform distribution on `X`: `ν(x) = 1 / |X|`.
    thm:conclusion-section-ledger-kl-identity -/
noncomputable def uniform : X → ℝ :=
  fun _ => 1 / (Fintype.card X : ℝ)

/-- KL divergence (Real-valued, not requiring `ν(x) > 0`).
    thm:conclusion-section-ledger-kl-identity -/
noncomputable def klDivergence (ν p : X → ℝ) : ℝ :=
  ∑ x, ν x * Real.log (ν x / p x)

omit [Nonempty X] in
/-- The uniform distribution at any point.
    thm:conclusion-section-ledger-kl-identity -/
theorem uniform_eq (x : X) : (uniform : X → ℝ) x = 1 / (Fintype.card X : ℝ) := rfl

/-- Logarithm of `uniform/pushforward`: `log(N) - log(|X|·d(x))`.
    thm:conclusion-section-ledger-kl-identity -/
theorem log_uniform_div_pushforward (d : X → ℕ) (N : ℕ) (x : X)
    (hN : 0 < N) (hd : 0 < d x) :
    Real.log ((uniform : X → ℝ) x / pushforward d N x) =
      Real.log (N : ℝ) - Real.log ((Fintype.card X : ℝ) * (d x : ℝ)) := by
  unfold uniform pushforward
  have hcard_pos : (0 : ℝ) < (Fintype.card X : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hd_pos : (0 : ℝ) < (d x : ℝ) := by exact_mod_cast hd
  have hcard_ne : (Fintype.card X : ℝ) ≠ 0 := ne_of_gt hcard_pos
  have hN_ne : (N : ℝ) ≠ 0 := ne_of_gt hN_pos
  have hd_ne : (d x : ℝ) ≠ 0 := ne_of_gt hd_pos
  have heq : (1 / (Fintype.card X : ℝ)) / ((d x : ℝ) / (N : ℝ)) =
      (N : ℝ) / ((Fintype.card X : ℝ) * (d x : ℝ)) := by
    field_simp
  rw [heq, Real.log_div hN_ne (by positivity)]

/-- Section ledger KL identity (core form).
    thm:conclusion-section-ledger-kl-identity -/
theorem section_ledger_kl_identity (d : X → ℕ) (N : ℕ)
    (hN : 0 < N) (hd : ∀ x, 0 < d x) :
    (1 / (Fintype.card X : ℝ)) * (∑ x, Real.log (d x : ℝ)) =
      Real.log ((N : ℝ) / (Fintype.card X : ℝ)) -
        klDivergence uniform (pushforward d N) := by
  have hcard_pos : (0 : ℝ) < (Fintype.card X : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hcard_ne : (Fintype.card X : ℝ) ≠ 0 := ne_of_gt hcard_pos
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hN_ne : (N : ℝ) ≠ 0 := ne_of_gt hN_pos
  -- Compute klDivergence directly.
  have hkl_expand : klDivergence uniform (pushforward d N) =
      ∑ x, (1 / (Fintype.card X : ℝ)) *
        (Real.log (N : ℝ) - Real.log ((Fintype.card X : ℝ) * (d x : ℝ))) := by
    unfold klDivergence
    apply Finset.sum_congr rfl
    intro x _
    have h := log_uniform_div_pushforward d N x hN (hd x)
    unfold uniform at h ⊢
    rw [h]
  rw [hkl_expand]
  -- Simplify the sum.
  rw [show (∑ x : X, (1 / (Fintype.card X : ℝ)) *
        (Real.log (N : ℝ) - Real.log ((Fintype.card X : ℝ) * (d x : ℝ)))) =
      (1 / (Fintype.card X : ℝ)) *
        ∑ x : X, (Real.log (N : ℝ) - Real.log ((Fintype.card X : ℝ) * (d x : ℝ)))
      from (Finset.mul_sum _ _ _).symm]
  -- Split the inner sum: ∑ (log N - log(card · d x))
  rw [Finset.sum_sub_distrib]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- Expand log (card · d x) = log card + log (d x)
  have hsum_log : (∑ x : X, Real.log ((Fintype.card X : ℝ) * (d x : ℝ))) =
      (Fintype.card X : ℝ) * Real.log (Fintype.card X : ℝ) +
        ∑ x : X, Real.log (d x : ℝ) := by
    have : ∀ x : X, Real.log ((Fintype.card X : ℝ) * (d x : ℝ)) =
        Real.log (Fintype.card X : ℝ) + Real.log (d x : ℝ) := by
      intro x
      have hd_pos : (0 : ℝ) < (d x : ℝ) := by exact_mod_cast hd x
      exact Real.log_mul hcard_ne (ne_of_gt hd_pos)
    rw [Finset.sum_congr rfl (fun x _ => this x)]
    rw [Finset.sum_add_distrib]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hsum_log]
  -- Now: goal = (1/card) · ∑ log d(x) = log(N/card) - (1/card) · (card·log N - (card·log card + ∑ log d(x)))
  have hlog_div : Real.log ((N : ℝ) / (Fintype.card X : ℝ)) =
      Real.log (N : ℝ) - Real.log (Fintype.card X : ℝ) :=
    Real.log_div hN_ne hcard_ne
  rw [hlog_div]
  field_simp
  ring

/-- Equivalent form: `∑ log d(x) = card · (log(N/card) - KL)`.
    thm:conclusion-section-ledger-kl-identity -/
theorem log_section_count_eq (d : X → ℕ) (N : ℕ)
    (hN : 0 < N) (hd : ∀ x, 0 < d x) :
    ∑ x, Real.log (d x : ℝ) =
      (Fintype.card X : ℝ) *
        (Real.log ((N : ℝ) / (Fintype.card X : ℝ)) -
          klDivergence uniform (pushforward d N)) := by
  have h := section_ledger_kl_identity d N hN hd
  have hcard_pos : (0 : ℝ) < (Fintype.card X : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hcard_ne : (Fintype.card X : ℝ) ≠ 0 := ne_of_gt hcard_pos
  have h2 : (Fintype.card X : ℝ) *
      ((1 / (Fintype.card X : ℝ)) * (∑ x, Real.log (d x : ℝ))) =
      ∑ x, Real.log (d x : ℝ) := by
    field_simp
  rw [← h2]
  rw [h]

/-- Paper package: section ledger KL identity.
    thm:conclusion-section-ledger-kl-identity -/
theorem paper_conclusion_section_ledger_kl_identity (d : X → ℕ) (N : ℕ)
    (hN : 0 < N) (hd : ∀ x, 0 < d x) :
    (1 / (Fintype.card X : ℝ)) * (∑ x, Real.log (d x : ℝ)) =
      Real.log ((N : ℝ) / (Fintype.card X : ℝ)) -
        klDivergence uniform (pushforward d N) :=
  section_ledger_kl_identity d N hN hd

end Omega.Conclusion.SectionLedgerKL
