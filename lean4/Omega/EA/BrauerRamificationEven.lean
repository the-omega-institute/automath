import Mathlib.Tactic

namespace Omega.EA

/-- Sum of constant halves over `S` equals `|S| / 2`.
    thm:prime-register-brauer-ramification-even -/
theorem half_sum_eq_card_div_two (S : Finset ℕ) :
    (∑ _p ∈ S, (1 / 2 : ℚ)) = (S.card : ℚ) / 2 := by
  rw [Finset.sum_const, nsmul_eq_mul]
  ring

/-- The half-sum is an integer iff the cardinality is even.
    thm:prime-register-brauer-ramification-even -/
theorem half_sum_int_iff_card_even (S : Finset ℕ) :
    (∃ n : ℤ, (∑ _p ∈ S, (1 / 2 : ℚ)) = n) ↔ Even S.card := by
  rw [half_sum_eq_card_div_two]
  constructor
  · rintro ⟨n, hn⟩
    -- hn : (S.card : ℚ) / 2 = n, so S.card = 2*n as a rational, hence 2 ∣ S.card
    have hcard : (S.card : ℚ) = 2 * (n : ℚ) := by
      field_simp at hn
      linarith
    have hN : (S.card : ℤ) = 2 * n := by exact_mod_cast hcard
    refine ⟨n.toNat, ?_⟩
    -- We need: S.card = n.toNat + n.toNat
    have hnn : 0 ≤ n := by
      have : (0 : ℤ) ≤ S.card := Int.natCast_nonneg _
      omega
    have : (S.card : ℤ) = n + n := by linarith
    have hcardNat : S.card = n.toNat + n.toNat := by
      have h1 : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hnn
      omega
    exact hcardNat
  · rintro ⟨k, hk⟩
    refine ⟨(k : ℤ), ?_⟩
    rw [hk]
    push_cast
    ring

/-- The reciprocity direction: integer half-sum forces even cardinality.
    thm:prime-register-brauer-ramification-even -/
theorem reciprocity_forces_even_card (S : Finset ℕ)
    (hsum : ∃ n : ℤ, (∑ _p ∈ S, (1 / 2 : ℚ)) = n) :
    Even S.card :=
  (half_sum_int_iff_card_even S).mp hsum

/-- Converse: even cardinality gives an integer half-sum.
    thm:prime-register-brauer-ramification-even -/
theorem even_card_gives_int_half_sum (S : Finset ℕ) (h : Even S.card) :
    ∃ n : ℤ, (∑ _p ∈ S, (1 / 2 : ℚ)) = n :=
  (half_sum_int_iff_card_even S).mpr h

/-- Paper package: Brauer-group ramification even-parity core identity.
    thm:prime-register-brauer-ramification-even -/
theorem paper_prime_register_brauer_ramification_even :
    (∀ S : Finset ℕ, (∑ _p ∈ S, (1 / 2 : ℚ)) = (S.card : ℚ) / 2) ∧
    (∀ S : Finset ℕ,
      (∃ n : ℤ, (∑ _p ∈ S, (1 / 2 : ℚ)) = n) ↔ Even S.card) ∧
    (∀ S : Finset ℕ,
      (∃ n : ℤ, (∑ _p ∈ S, (1 / 2 : ℚ)) = n) → Even S.card) ∧
    (∀ S : Finset ℕ, Even S.card →
      ∃ n : ℤ, (∑ _p ∈ S, (1 / 2 : ℚ)) = n) :=
  ⟨half_sum_eq_card_div_two,
   half_sum_int_iff_card_even,
   reciprocity_forces_even_card,
   even_card_gives_int_half_sum⟩

end Omega.EA
