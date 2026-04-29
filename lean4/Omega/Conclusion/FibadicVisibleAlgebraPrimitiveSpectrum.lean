import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete exact-depth coordinate data for the visible fibadic algebra package. -/
structure conclusion_fibadic_visible_algebra_primitive_spectrum_data where
  conclusion_fibadic_visible_algebra_primitive_spectrum_exactDepthRank : ℕ → ℕ

/-- Coordinates whose exact-depth rank is nonzero. -/
def conclusion_fibadic_visible_algebra_primitive_spectrum_data.primitiveSpectrum
    (D : conclusion_fibadic_visible_algebra_primitive_spectrum_data) : Set ℕ :=
  {n | 0 < D.conclusion_fibadic_visible_algebra_primitive_spectrum_exactDepthRank n}

/-- The primitive spectrum is the set of nonzero exact-depth coordinates. -/
def conclusion_fibadic_visible_algebra_primitive_spectrum_data.primitiveSpectrumIdentified
    (D : conclusion_fibadic_visible_algebra_primitive_spectrum_data) : Prop :=
  D.primitiveSpectrum =
    {n | D.conclusion_fibadic_visible_algebra_primitive_spectrum_exactDepthRank n ≠ 0}

/-- Distinct appearance ranks are separated by the exact-depth coordinate function. -/
def conclusion_fibadic_visible_algebra_primitive_spectrum_data.exactDepthSeparatesQuotients
    (D : conclusion_fibadic_visible_algebra_primitive_spectrum_data) : Prop :=
  ∀ a b,
    D.conclusion_fibadic_visible_algebra_primitive_spectrum_exactDepthRank a ≠
      D.conclusion_fibadic_visible_algebra_primitive_spectrum_exactDepthRank b →
      ∃ coordinate : ℕ → ℕ,
        coordinate a ≠ coordinate b ∧
          ∀ n, coordinate n =
            D.conclusion_fibadic_visible_algebra_primitive_spectrum_exactDepthRank n

/-- Paper label: `thm:conclusion-fibadic-visible-algebra-primitive-spectrum`. -/
theorem paper_conclusion_fibadic_visible_algebra_primitive_spectrum
    (D : conclusion_fibadic_visible_algebra_primitive_spectrum_data) :
    D.primitiveSpectrumIdentified ∧ D.exactDepthSeparatesQuotients := by
  constructor
  · ext n
    simp [conclusion_fibadic_visible_algebra_primitive_spectrum_data.primitiveSpectrum,
      Nat.pos_iff_ne_zero]
  · intro a b hab
    refine ⟨D.conclusion_fibadic_visible_algebra_primitive_spectrum_exactDepthRank, hab, ?_⟩
    intro n
    rfl

end Omega.Conclusion
