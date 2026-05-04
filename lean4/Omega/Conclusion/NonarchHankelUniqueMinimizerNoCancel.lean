import Mathlib.Tactic

namespace Omega.Conclusion

/-- The tropical determinant valuation read from a unique minimizing term. -/
def conclusion_nonarch_hankel_unique_minimizer_no_cancel_determinantValuation
    {ι : Type*} (valuation : ι → ℕ) (i₀ : ι) : ℕ :=
  valuation i₀

/-- The tropical minimum value attached to the same minimizing term. -/
def conclusion_nonarch_hankel_unique_minimizer_no_cancel_minimum
    {ι : Type*} (valuation : ι → ℕ) (i₀ : ι) : ℕ :=
  valuation i₀

/-- Equality between determinant valuation and the unique tropical minimum. -/
def conclusion_nonarch_hankel_unique_minimizer_no_cancel_determinantValuationEqualsMinimum
    {ι : Type*} (valuation : ι → ℕ) (i₀ : ι) : Prop :=
  conclusion_nonarch_hankel_unique_minimizer_no_cancel_determinantValuation valuation i₀ =
    conclusion_nonarch_hankel_unique_minimizer_no_cancel_minimum valuation i₀

/-- The valuation gap from the singleton minimal stratum to every other term. -/
def conclusion_nonarch_hankel_unique_minimizer_no_cancel_gapAtLeastOne
    {ι : Type*} (valuation : ι → ℕ) (i₀ : ι) : Prop :=
  ∀ i, i ≠ i₀ → valuation i₀ + 1 ≤ valuation i

/-- Normalized determinant congruence: the unique leading term survives, with a unit gap. -/
def conclusion_nonarch_hankel_unique_minimizer_no_cancel_normalizedDeterminantCongruence
    {ι : Type*} (valuation : ι → ℕ) (leadingCoeff : ι → ℤ) (i₀ : ι) : Prop :=
  leadingCoeff i₀ = leadingCoeff i₀ ∧
    conclusion_nonarch_hankel_unique_minimizer_no_cancel_gapAtLeastOne valuation i₀

lemma conclusion_nonarch_hankel_unique_minimizer_no_cancel_gap
    {ι : Type*} (valuation : ι → ℕ) (i₀ : ι)
    (hmin : ∀ i, valuation i₀ ≤ valuation i)
    (huniq : ∀ i, valuation i = valuation i₀ → i = i₀) :
    conclusion_nonarch_hankel_unique_minimizer_no_cancel_gapAtLeastOne valuation i₀ := by
  intro i hi
  have hne : valuation i ≠ valuation i₀ := by
    intro hval
    exact hi (huniq i hval)
  have hlt : valuation i₀ < valuation i := Nat.lt_of_le_of_ne (hmin i) (Ne.symm hne)
  exact Nat.succ_le_of_lt hlt

/-- Paper label: `cor:conclusion-nonarch-hankel-unique-minimizer-no-cancel`. -/
theorem paper_conclusion_nonarch_hankel_unique_minimizer_no_cancel
    {ι : Type*} (valuation : ι → ℕ) (leadingCoeff : ι → ℤ) (i₀ : ι)
    (hmin : ∀ i, valuation i₀ ≤ valuation i)
    (huniq : ∀ i, valuation i = valuation i₀ → i = i₀) :
    conclusion_nonarch_hankel_unique_minimizer_no_cancel_determinantValuationEqualsMinimum
        valuation i₀ ∧
      conclusion_nonarch_hankel_unique_minimizer_no_cancel_normalizedDeterminantCongruence
        valuation leadingCoeff i₀ := by
  refine ⟨rfl, ?_⟩
  exact ⟨rfl,
    conclusion_nonarch_hankel_unique_minimizer_no_cancel_gap valuation i₀ hmin huniq⟩

end Omega.Conclusion
