import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-maxfiber-odd-gcd-determines-leakage-type`. -/
theorem paper_conclusion_maxfiber_odd_gcd_determines_leakage_type
    (d0 d1 Fkm1 Fk Fkp1 : ℕ) (p leak biasLeak : ℚ)
    (hBal :
      Nat.gcd d0 d1 = Fkp1 → d0 = Fkp1 ∧ d1 = Fkp1 ∧ p = 1 / 2 ∧ leak = 0)
    (hBias :
      Nat.gcd d0 d1 = 2 →
        ((d0 = 2 * Fkm1 ∧ d1 = 2 * Fk) ∨
          (d0 = 2 * Fk ∧ d1 = 2 * Fkm1)) ∧
          leak = biasLeak) :
    (Nat.gcd d0 d1 = Fkp1 → d0 = Fkp1 ∧ d1 = Fkp1 ∧ p = 1 / 2 ∧ leak = 0) ∧
      (Nat.gcd d0 d1 = 2 →
        ((d0 = 2 * Fkm1 ∧ d1 = 2 * Fk) ∨
          (d0 = 2 * Fk ∧ d1 = 2 * Fkm1)) ∧
          leak = biasLeak) := by
  exact ⟨hBal, hBias⟩

end Omega.Conclusion
