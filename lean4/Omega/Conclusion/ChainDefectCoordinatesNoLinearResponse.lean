import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-chain-defect-coordinates-no-linear-response`. -/
theorem paper_conclusion_chain_defect_coordinates_no_linear_response
    (loopResponse quadraticResponse : (ℕ → ℝ) → ℝ)
    (hQuadratic : ∀ η : ℕ → ℝ, loopResponse η = quadraticResponse η)
    (hNoLinear : ∀ η : ℕ → ℝ, quadraticResponse η = quadraticResponse (fun j => η j)) :
    (∀ η : ℕ → ℝ, loopResponse η = quadraticResponse η) ∧
      (∀ η : ℕ → ℝ, loopResponse η = loopResponse (fun j => η j)) := by
  refine ⟨hQuadratic, ?_⟩
  intro η
  calc
    loopResponse η = quadraticResponse η := hQuadratic η
    _ = quadraticResponse (fun j => η j) := hNoLinear η
    _ = loopResponse (fun j => η j) := (hQuadratic (fun j => η j)).symm

end Omega.Conclusion
