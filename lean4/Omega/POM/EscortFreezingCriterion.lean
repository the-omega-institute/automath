import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `cor:pom-escort-freezing-criterion`.

The formal algebraic core of the freezing criterion: zero escort min-entropy is the
corresponding pressure equality, and vanishing multiplicative entropy loss is the same as the
pure-power pressure equality on every multiplier. -/
theorem paper_pom_escort_freezing_criterion
    (pressure : ℕ → ℝ) (alphaStar : ℝ) (a : ℕ) (ha : 1 ≤ a) :
    let escortMinEntropyLoss : ℝ := pressure a - (a : ℝ) * alphaStar
    let multiplicativeEntropyLoss : ℕ → ℝ :=
      fun b => (b : ℝ) * pressure a - pressure (a * b)
    (escortMinEntropyLoss = 0 ↔ pressure a = (a : ℝ) * alphaStar) ∧
      (∀ b : ℕ, 2 ≤ b →
        (multiplicativeEntropyLoss b = 0 ↔
          pressure (a * b) = (b : ℝ) * pressure a)) ∧
      ((∀ b : ℕ, 2 ≤ b → multiplicativeEntropyLoss b = 0) ↔
        ∀ b : ℕ, 2 ≤ b → pressure (a * b) = (b : ℝ) * pressure a) := by
  have _ha : 1 ≤ a := ha
  dsimp
  have hmin : pressure a - (a : ℝ) * alphaStar = 0 ↔
      pressure a = (a : ℝ) * alphaStar := by
    constructor <;> intro h <;> nlinarith
  have hloss : ∀ b : ℕ, 2 ≤ b →
      ((b : ℝ) * pressure a - pressure (a * b) = 0 ↔
        pressure (a * b) = (b : ℝ) * pressure a) := by
    intro b _hb
    constructor <;> intro h <;> nlinarith
  refine ⟨hmin, hloss, ?_⟩
  constructor
  · intro hzero b hb
    exact (hloss b hb).mp (hzero b hb)
  · intro hpure b hb
    exact (hloss b hb).mpr (hpure b hb)

end Omega.POM
