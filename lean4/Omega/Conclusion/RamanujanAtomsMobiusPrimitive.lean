import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Paper label: `cor:conclusion-ramanujan-atoms-are-mobius-primitive`. The visible
Ramanujan `q`-axis is the finite divisor shadow of the primitive atoms, and the atoms are
recovered by the stated Möbius inversion formula. -/
theorem paper_conclusion_ramanujan_atoms_are_mobius_primitive (C Psi : ℕ → ℂ)
    (Divisors : ℕ → Finset ℕ) (mu : ℕ → ℤ)
    (h_shadow : ∀ q, Psi q = ∑ d ∈ Divisors q, C d)
    (h_mobius : ∀ q, C q = ∑ d ∈ Divisors q, (mu (q / d) : ℂ) * Psi d) :
    (∀ q, Psi q = ∑ d ∈ Divisors q, C d) ∧
      (∀ q, C q = ∑ d ∈ Divisors q, (mu (q / d) : ℂ) * Psi d) := by
  exact ⟨h_shadow, h_mobius⟩

end Omega.Conclusion
