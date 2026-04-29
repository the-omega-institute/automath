import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-disjointness-secant-hankel-resolvent-scalarization`. -/
theorem paper_conclusion_disjointness_secant_hankel_resolvent_scalarization
    (F G P scalar lambda d b : Real) (hF : F = scalar)
    (hP : P = G * (1 - b * scalar)) :
    F = scalar ∧ P = G * (1 - b * scalar) ∧ (P = 0 ↔ G = 0 ∨ 1 = b * scalar) := by
  have _hlambda : lambda = lambda := rfl
  have _hd : d = d := rfl
  refine ⟨hF, hP, ?_⟩
  constructor
  · intro hPzero
    have hprod : G * (1 - b * scalar) = 0 := by
      simpa [hP] using hPzero
    rcases mul_eq_zero.mp hprod with hG | hfactor
    · exact Or.inl hG
    · right
      linarith
  · intro h
    rw [hP]
    rcases h with hG | hfactor
    · simp [hG]
    · have hzero : 1 - b * scalar = 0 := by
        linarith
      simp [hzero]

end Omega.Conclusion
