import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-toeplitz-negative-parity-local-rigidity`. -/
theorem paper_conclusion_toeplitz_negative_parity_local_rigidity
    (κ : ℕ) (detT detR detP detHsq : ℝ)
    (hdet : detT = detR * detP * (-1 : ℝ) ^ κ * detHsq)
    (hR : 0 < detR) (hP : 0 < detP) (hH : 0 < detHsq) :
    (0 < detT ↔ Even κ) ∧ (detT < 0 ↔ Odd κ) := by
  rcases Nat.even_or_odd κ with hκ | hκ
  · have hpow : (-1 : ℝ) ^ κ = 1 := by
      simpa using hκ.neg_one_pow
    have hdet_pos : 0 < detT := by
      rw [hdet, hpow]
      ring_nf
      exact mul_pos (mul_pos hR hP) hH
    refine ⟨?_, ?_⟩
    · constructor
      · intro _h
        exact hκ
      · intro _h
        exact hdet_pos
    · constructor
      · intro hneg
        linarith
      · intro hodd
        rcases hκ with ⟨a, ha⟩
        rcases hodd with ⟨b, hb⟩
        omega
  · have hpow : (-1 : ℝ) ^ κ = -1 := by
      simpa using hκ.neg_one_pow
    have hdet_neg : detT < 0 := by
      rw [hdet, hpow]
      ring_nf
      have hprod : 0 < detR * detP * detHsq := mul_pos (mul_pos hR hP) hH
      linarith
    refine ⟨?_, ?_⟩
    · constructor
      · intro hpos
        linarith
      · intro heven
        rcases heven with ⟨a, ha⟩
        rcases hκ with ⟨b, hb⟩
        omega
    · constructor
      · intro _h
        exact hκ
      · intro _h
        exact hdet_neg

end Omega.Conclusion
