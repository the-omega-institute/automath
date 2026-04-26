import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-shell-escort-fourchamber-phase-diagram`. -/
theorem paper_conclusion_window6_shell_escort_fourchamber_phase_diagram
    (q34 q24 q23 : ℝ) (mu2 mu3 mu4 : ℝ → ℝ)
    (horder : q34 < q24 ∧ q24 < 0 ∧ 0 < q23)
    (h34 : ∀ q, q < q34 → mu3 q > mu4 q)
    (h34' : ∀ q, q34 < q → mu4 q > mu3 q)
    (h24 : ∀ q, q < q24 → mu2 q > mu4 q)
    (h24' : ∀ q, q24 < q → mu4 q > mu2 q)
    (h23 : ∀ q, q < q23 → mu2 q > mu3 q)
    (h23' : ∀ q, q23 < q → mu3 q > mu2 q) :
    q34 < q24 ∧ q24 < 0 ∧ 0 < q23 ∧
      (∀ q, q < q34 → mu2 q > mu3 q ∧ mu3 q > mu4 q) ∧
      (∀ q, q34 < q → q < q24 → mu2 q > mu4 q ∧ mu4 q > mu3 q) ∧
      (∀ q, q24 < q → q < q23 → mu4 q > mu2 q ∧ mu2 q > mu3 q) ∧
      (∀ q, q23 < q → mu4 q > mu3 q ∧ mu3 q > mu2 q) := by
  rcases horder with ⟨h3424, h240, h0_23⟩
  refine ⟨h3424, h240, h0_23, ?_, ?_, ?_, ?_⟩
  · intro q hq
    have hq23 : q < q23 := by linarith
    exact ⟨h23 q hq23, h34 q hq⟩
  · intro q hq34 hq24
    exact ⟨h24 q hq24, h34' q hq34⟩
  · intro q hq24 hq23
    exact ⟨h24' q hq24, h23 q hq23⟩
  · intro q hq23
    have hq34 : q34 < q := by linarith
    exact ⟨h34' q hq34, h23' q hq23⟩

end Omega.Conclusion
