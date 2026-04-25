import Omega.Conclusion.Window6Collision

namespace Omega.Conclusion

/-- Paper-facing wrapper for the window-`6` q-moment triple and its strict likelihood-ratio
monotonicity certificates.
    `thm:conclusion-window6-qmoment-triple-geometry` -/
theorem paper_conclusion_window6_qmoment_triple_geometry :
    8 + 4 + 9 = 21 ∧
      8 * 2 + 4 * 3 + 9 * 4 = 64 ∧
      8 * 2 ^ 2 + 4 * 3 ^ 2 + 9 * 4 ^ 2 = 212 ∧
      StrictMono (fun q : Nat => ((9 : ℚ) * (4 : ℚ)^q) / ((8 : ℚ) * (2 : ℚ)^q)) ∧
      StrictMono (fun q : Nat => ((4 : ℚ) * (3 : ℚ)^q) / ((8 : ℚ) * (2 : ℚ)^q)) := by
  rcases window6_qmoment_triple with ⟨h0, h1, _⟩
  exact ⟨h0, h1, window6_S2_wedderburn, window6_lr_four_vs_two_strictMono,
    window6_lr_three_vs_two_strictMono⟩

end Omega.Conclusion
