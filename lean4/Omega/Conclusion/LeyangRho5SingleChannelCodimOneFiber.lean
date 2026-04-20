import Omega.Conclusion.LeyangS5TwoChannelMinimalCompleteness

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-leyang-rho5-single-channel-codim-one-fiber`.
Keeping the `ρ₅` coordinates fixed leaves exactly one affine degree of freedom: transfer mass
between the `(2·1^3)` and `(2^2·1)` coordinates while preserving their sum. -/
theorem paper_conclusion_leyang_rho5_single_channel_codim_one_fiber (v : LeyangS5DensityVector)
    (hv : Omega.Conclusion.IsNormalizedDensity v) :
    ∃ line : ℚ → Omega.Conclusion.LeyangS5DensityVector,
      line 0 = v ∧
      (∀ t, Omega.Conclusion.IsNormalizedDensity (line t)) ∧
      (∀ t, Omega.Conclusion.rho5Coordinates (line t) = Omega.Conclusion.rho5Coordinates v) ∧
      (∀ s t, line s = line t ↔ s = t) := by
  let line : ℚ → LeyangS5DensityVector := fun t i =>
    if i = 1 then v 1 - t else if i = 2 then v 2 + t else v i
  refine ⟨line, ?_, ?_, ?_, ?_⟩
  · ext i
    fin_cases i <;> simp [line]
  · intro t
    dsimp [IsNormalizedDensity]
    calc
      line t 0 + line t 1 + line t 2 + line t 3 + line t 4 + line t 5 + line t 6
          = v 0 + v 1 + v 2 + v 3 + v 4 + v 5 + v 6 := by
              simp [line]
              ring
      _ = 1 := hv
  · intro t
    simp [rho5Coordinates, line]
  · intro s t
    constructor
    · intro h
      have h2 := congrArg (fun w : LeyangS5DensityVector => w 2) h
      simp [line] at h2
      linarith
    · intro hst
      subst hst
      rfl

end Omega.Conclusion
