import Mathlib.Tactic

theorem paper_conclusion_fiber_nogap_spectrum_purely_spectral_bias (R q : ℕ)
    (hq : q ≤ R + 1) :
    ∀ a : Fin q, ∃ j : Fin (R + 1), j.1 % q = a.1 := by
  intro a
  refine ⟨⟨a.1, lt_of_lt_of_le a.2 hq⟩, ?_⟩
  exact Nat.mod_eq_of_lt a.2

