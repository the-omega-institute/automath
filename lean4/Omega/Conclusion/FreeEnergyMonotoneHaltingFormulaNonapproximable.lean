import Mathlib.Tactic

namespace Omega.Conclusion

/-- Any rational interval approximator with width strictly smaller than the spectral gap would
separate the two possible free-energy values and therefore decide the halting predicate, which
contradicts undecidability.
    thm:conclusion-free-energy-monotone-halting-formula-nonapproximable -/
theorem paper_conclusion_free_energy_monotone_halting_formula_nonapproximable {Code : Type*}
    (halts : Code → Prop) (freeEnergy : Code → ℝ) (a b δ : ℝ)
    (hSep : 0 < δ ∧ δ < (b - a) / 2) (hZero : ∀ c, ¬ halts c ↔ freeEnergy c = a)
    (hOne : ∀ c, halts c ↔ freeEnergy c = b)
    (hUndecidable : ¬ Nonempty (∀ c, Decidable (halts c))) :
    ¬ ∃ approx : Code → ℚ × ℚ,
      ∀ c,
        ((approx c).1 : ℝ) ≤ freeEnergy c ∧ freeEnergy c ≤ (approx c).2 ∧
          (((approx c).2 : ℝ) - (approx c).1) < δ := by
  intro hApprox
  rcases hApprox with ⟨approx, happrox⟩
  apply hUndecidable
  refine ⟨fun c => ?_⟩
  let I : Prop := ((approx c).1 : ℝ) ≤ b ∧ b ≤ (approx c).2
  have hIff : halts c ↔ I := by
    constructor
    · intro hHalt
      have hEq : freeEnergy c = b := (hOne c).1 hHalt
      rcases happrox c with ⟨hlo, hhi, _⟩
      simpa [I, hEq] using And.intro hlo hhi
    · intro hI
      by_contra hNotHalt
      have hEqA : freeEnergy c = a := (hZero c).1 hNotHalt
      rcases happrox c with ⟨hlo, hhi, hwidth⟩
      have hGapLe :
          b - a ≤ ((approx c).2 : ℝ) - (approx c).1 := by
        rcases hI with ⟨hblo, hbhi⟩
        linarith
      have hδlt : δ < b - a := by
        linarith
      linarith
  exact decidable_of_iff I hIff.symm

end Omega.Conclusion
