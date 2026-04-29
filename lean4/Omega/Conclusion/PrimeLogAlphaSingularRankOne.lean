import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-prime-log-alpha-singular-rank-one`. Subtracting two
Abel--Mellin decompositions isolates the singular dependence on the shared zeta factor, with the
regular remainder given by the difference of the holomorphic parts. -/
theorem paper_conclusion_prime_log_alpha_singular_rank_one
    (D1 D2 J1 J2 ζ : ℂ → ℂ) (c1 c2 : ℂ)
    (h1 : ∀ s : ℂ, D1 s = c1 * ζ s + J1 s)
    (h2 : ∀ s : ℂ, D2 s = c2 * ζ s + J2 s) :
    ∃ H12 : ℂ → ℂ, ∀ s : ℂ, D1 s - D2 s = (c1 - c2) * ζ s + H12 s := by
  refine ⟨fun s => J1 s - J2 s, ?_⟩
  intro s
  calc
    D1 s - D2 s = (c1 * ζ s + J1 s) - (c2 * ζ s + J2 s) := by rw [h1 s, h2 s]
    _ = (c1 - c2) * ζ s + (J1 s - J2 s) := by ring

end Omega.Conclusion
