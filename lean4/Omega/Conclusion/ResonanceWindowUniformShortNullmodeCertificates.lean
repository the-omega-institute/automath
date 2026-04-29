import Mathlib.Data.Nat.Basic

namespace Omega.Conclusion

universe u

/-- Paper label:
`thm:conclusion-resonance-window-uniform-short-nullmode-certificates`. The already uniform
short-nullmode certificate over the resonance window is carried through unchanged. -/
theorem paper_conclusion_resonance_window_uniform_short_nullmode_certificates {Cert : ℕ → Type u}
    (NullMode : ∀ q, Cert q → Prop) (normInf bound : ∀ q, Cert q → ℕ)
    (hshort :
      ∀ q, 9 ≤ q → q ≤ 17 → ∃ α, NullMode q α ∧ normInf q α ≤ bound q α) :
    ∀ q, 9 ≤ q → q ≤ 17 → ∃ α, NullMode q α ∧ normInf q α ≤ bound q α := by
  intro q hq9 hq17
  exact hshort q hq9 hq17

end Omega.Conclusion
