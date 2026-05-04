import Omega.Zeta.SymqGoldenCqIntegerSmithMultiplicitySpectrum

namespace Omega.Zeta

/-- Paper label: `thm:xi-symq-golden-cq-mod5-second-difference-smith`. -/
theorem paper_xi_symq_golden_cq_mod5_second_difference_smith (m : ℕ) (hm : 1 ≤ m) :
    (∀ t : ℕ, 1 ≤ t → t < m →
      Omega.Zeta.xi_symq_golden_cq_integer_smith_multiplicity_spectrum_mult (2 * m) t = 4) ∧
    Omega.Zeta.xi_symq_golden_cq_integer_smith_multiplicity_spectrum_mult (2 * m) m = 3 ∧
    (∀ t : ℕ, m + 1 ≤ t →
      Omega.Zeta.xi_symq_golden_cq_integer_smith_multiplicity_spectrum_mult (2 * m) t = 0) ∧
    (∀ t : ℕ, 1 ≤ t → t ≤ m →
      Omega.Zeta.xi_symq_golden_cq_integer_smith_multiplicity_spectrum_mult
        (2 * m + 1) t = 4) ∧
    Omega.Zeta.xi_symq_golden_cq_integer_smith_multiplicity_spectrum_mult
      (2 * m + 1) (m + 1) = 1 ∧
    (∀ t : ℕ, m + 2 ≤ t →
      Omega.Zeta.xi_symq_golden_cq_integer_smith_multiplicity_spectrum_mult
        (2 * m + 1) t = 0) := by
  rcases paper_xi_symq_golden_cq_integer_smith_multiplicity_spectrum m hm with
    ⟨_, heven, hevenTop, _, hodd, hoddTop⟩
  refine ⟨heven, hevenTop, ?_, hodd, hoddTop, ?_⟩
  · intro t ht
    have ht_ne_zero : t ≠ 0 := by omega
    have hnot_lt : ¬2 * t < 2 * m := by omega
    have hnot_eq : ¬2 * t = 2 * m := by omega
    have hnot_eq_succ : ¬2 * t = 2 * m + 1 := by omega
    simp [xi_symq_golden_cq_integer_smith_multiplicity_spectrum_mult, ht_ne_zero,
      hnot_lt, hnot_eq, hnot_eq_succ]
  · intro t ht
    have ht_ne_zero : t ≠ 0 := by omega
    have hnot_lt : ¬2 * t < 2 * m + 1 := by omega
    have hnot_eq : ¬2 * t = 2 * m + 1 := by omega
    have hnot_eq_succ : ¬2 * t = 2 * m + 1 + 1 := by omega
    simp [xi_symq_golden_cq_integer_smith_multiplicity_spectrum_mult, ht_ne_zero,
      hnot_lt, hnot_eq, hnot_eq_succ]

end Omega.Zeta
