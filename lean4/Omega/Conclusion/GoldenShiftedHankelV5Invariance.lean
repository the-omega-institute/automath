import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-golden-shifted-hankel-v5-invariance`. -/
theorem paper_conclusion_golden_shifted_hankel_v5_invariance (D : Int) (det : Nat -> Int)
    (v5 : Int -> Nat) (h_sign : ∀ r, det r = D ∨ det r = -D)
    (h_v5_neg : ∀ z, v5 (-z) = v5 z) :
    ∀ r, v5 (det r) = v5 D := by
  intro r
  rcases h_sign r with hdet | hdet
  · rw [hdet]
  · rw [hdet, h_v5_neg]

end Omega.Conclusion
