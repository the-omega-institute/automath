import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-primitive-two-step-codimone-blindness`. -/
theorem paper_conclusion_primitive_two_step_codimone_blindness {K : Type*} [Field K]
    (u : K) (p pcore : ℕ → K)
    (hdiff : ∀ n, p n - pcore n = if n = 2 then u else 0) (Λ : (ℕ → K) → K)
    (a2 : K)
    (hΛ : ∀ q q', (∀ n, n ≠ 2 → q n = q' n) →
      Λ q - Λ q' = a2 * (q 2 - q' 2)) :
    (∀ n, n ≠ 2 → p n = pcore n) ∧ Λ p - Λ pcore = a2 * u := by
  have hcoord : ∀ n, n ≠ 2 → p n = pcore n := by
    intro n hn
    have hzero : p n - pcore n = 0 := by
      simpa [if_neg hn] using hdiff n
    exact sub_eq_zero.mp hzero
  constructor
  · exact hcoord
  · have hΛp := hΛ p pcore hcoord
    have h2 : p 2 - pcore 2 = u := by
      simpa using hdiff 2
    calc
      Λ p - Λ pcore = a2 * (p 2 - pcore 2) := hΛp
      _ = a2 * u := by rw [h2]

end Omega.Conclusion
