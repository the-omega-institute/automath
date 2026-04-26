import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `thm:pom-microcanonical-escort-all-renyi-collapse`. -/
theorem paper_pom_microcanonical_escort_all_renyi_collapse
    (f : ℝ → ℝ) (uniformEntropy escortEntropy : ℝ → ℝ → ℝ) (a a0 a1 qstar : ℝ)
    (ha : a0 < a ∧ a < a1) (hqstar : 0 < qstar ∧ qstar < 1)
    (hUniform : ∀ b : ℝ, 0 < b → uniformEntropy a b = f a)
    (hEscort : ∀ b : ℝ, 0 < b → escortEntropy a b = f a) :
    ∀ b : ℝ, 0 < b → uniformEntropy a b = escortEntropy a b ∧
      uniformEntropy a b = f a := by
  have _ : a0 < a ∧ a < a1 := ha
  have _ : 0 < qstar ∧ qstar < 1 := hqstar
  intro b hb
  exact ⟨(hUniform b hb).trans (hEscort b hb).symm, hUniform b hb⟩

end Omega.POM
