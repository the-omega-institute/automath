namespace Omega.Conclusion

universe u

theorem paper_conclusion_coldend_convex_hull_difference_window_prony_equivalence
    (ColdHull SupportFn DifferenceWindow : Type u) (Determines : Type u -> Type u -> Prop)
    (hHullSupport : Determines ColdHull SupportFn)
    (hSupportWindow : Determines SupportFn DifferenceWindow)
    (hWindowHull : Determines DifferenceWindow ColdHull) :
    Determines ColdHull SupportFn ∧ Determines SupportFn DifferenceWindow ∧
      Determines DifferenceWindow ColdHull := by
  exact ⟨hHullSupport, hSupportWindow, hWindowHull⟩

end Omega.Conclusion
