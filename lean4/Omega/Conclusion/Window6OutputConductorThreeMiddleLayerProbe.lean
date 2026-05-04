import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-window6-output-conductor-three-middle-layer-probe`. -/
theorem paper_conclusion_window6_output_conductor_three_middle_layer_probe
    (N3 N7 N21 : ℝ → ℝ)
    (hN3 : ∀ T, N3 T = if T < 2 then 0 else if T < 3 then 2 else 0)
    (hN7 : ∀ T, N7 T = if T < 2 then 0 else if T < 3 then 1 else if T < 4 then 5 else 0)
    (hN21 : ∀ T, N21 T = if T < 2 then 0 else if T < 3 then 5 else if T < 4 then 7 else 0) :
    (∀ T, 0 < T → T < 2 → N3 T = 0 ∧ N7 T = 0 ∧ N21 T = 0) ∧
      (∀ T, 2 < T → T < 3 → N3 T = 2 ∧ N7 T = 1 ∧ N21 T = 5) ∧
        (∀ T, 3 < T → T < 4 → N3 T = 0 ∧ N7 T = 5 ∧ N21 T = 7) ∧
          (∀ T, 4 < T → N3 T = 0 ∧ N7 T = 0 ∧ N21 T = 0) := by
  constructor
  · intro T _ hT2
    simp [hN3 T, hN7 T, hN21 T, hT2]
  constructor
  · intro T h2T hT3
    have hnot2 : ¬ T < 2 := by linarith
    simp [hN3 T, hN7 T, hN21 T, hnot2, hT3]
  constructor
  · intro T h3T hT4
    have hnot2 : ¬ T < 2 := by linarith
    have hnot3 : ¬ T < 3 := by linarith
    simp [hN3 T, hN7 T, hN21 T, hnot2, hnot3, hT4]
  · intro T h4T
    have hnot2 : ¬ T < 2 := by linarith
    have hnot3 : ¬ T < 3 := by linarith
    have hnot4 : ¬ T < 4 := by linarith
    simp [hN3 T, hN7 T, hN21 T, hnot2, hnot3, hnot4]

end Omega.Conclusion
