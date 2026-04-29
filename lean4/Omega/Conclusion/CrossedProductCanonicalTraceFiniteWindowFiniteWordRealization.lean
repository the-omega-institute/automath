import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-crossed-product-canonical-trace-finite-window-finite-word-realization`. -/
theorem paper_conclusion_crossed_product_canonical_trace_finite_window_finite_word_realization
    {α M : Type} [Monoid M] (exact : α → M) (approx : Nat → α → M) (Lstar : Nat)
    (hgen : ∀ L, Lstar ≤ L → ∀ a : α, approx L a = exact a) :
    ∀ L, Lstar ≤ L → ∀ w : List α, (w.map (approx L)).prod = (w.map exact).prod := by
  intro L hL w
  induction w with
  | nil =>
      simp
  | cons a w ih =>
      simp [hgen L hL a, ih]

end Omega.Conclusion
