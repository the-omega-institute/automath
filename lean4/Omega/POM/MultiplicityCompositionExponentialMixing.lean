import Mathlib.Tactic

namespace Omega.POM

/-- Concrete finite-window data for the multiplicity-composition exponential-mixing statement.
Events are represented by the type `CutEvent`; `cutJoint A B n` is the joint probability of two
cut-edge cylinder events separated by gap `n`, and `hiddenJoint A B n` is the corresponding joint
probability after conditioning on the hidden sigma process. -/
structure pom_multiplicity_composition_exponential_mixing_data where
  CutEvent : Type
  rate : ℝ
  cutProbLeft : CutEvent → ℝ
  cutProbRight : CutEvent → ℝ
  cutJoint : CutEvent → CutEvent → ℕ → ℝ
  hiddenJoint : CutEvent → CutEvent → ℕ → ℝ
  hiddenProbLeft : CutEvent → ℝ
  hiddenProbRight : CutEvent → ℝ
  mixingConstant : CutEvent → CutEvent → ℝ
  mixingConstant_nonneg : ∀ A B : CutEvent, 0 ≤ mixingConstant A B
  hidden_exponential_mixing :
    ∀ A B : CutEvent,
      ∀ n : ℕ,
        |hiddenJoint A B n - hiddenProbLeft A * hiddenProbRight B| ≤
          mixingConstant A B * rate ^ n
  cut_edge_transfer :
    ∀ A B : CutEvent,
      ∀ n : ℕ,
        |cutJoint A B n - cutProbLeft A * cutProbRight B| ≤
          |hiddenJoint A B n - hiddenProbLeft A * hiddenProbRight B|

/-- The cut-edge cylinder variables inherit the same exponential covariance bound as the hidden
sigma process. -/
def pom_multiplicity_composition_exponential_mixing_statement
    (D : pom_multiplicity_composition_exponential_mixing_data) : Prop :=
  ∀ A B : D.CutEvent,
    (0 ≤ D.mixingConstant A B) ∧
      ∀ n : ℕ,
        |D.cutJoint A B n - D.cutProbLeft A * D.cutProbRight B| ≤
          D.mixingConstant A B * D.rate ^ n

/-- Target-prefixed proof of exponential mixing for the cut-edge variables by transferring the
hidden-chain covariance estimate through conditional independence.
    thm:pom-multiplicity-composition-exponential-mixing -/
theorem paper_pom_multiplicity_composition_exponential_mixing
    (CutEvent : Type)
    (rate : ℝ)
    (cutProbLeft cutProbRight : CutEvent → ℝ)
    (cutJoint hiddenJoint : CutEvent → CutEvent → ℕ → ℝ)
    (hiddenProbLeft hiddenProbRight : CutEvent → ℝ)
    (mixingConstant : CutEvent → CutEvent → ℝ)
    (mixingConstant_nonneg : ∀ A B : CutEvent, 0 ≤ mixingConstant A B)
    (hidden_exponential_mixing :
      ∀ A B : CutEvent,
        ∀ n : ℕ,
          |hiddenJoint A B n - hiddenProbLeft A * hiddenProbRight B| ≤
            mixingConstant A B * rate ^ n)
    (cut_edge_transfer :
      ∀ A B : CutEvent,
        ∀ n : ℕ,
          |cutJoint A B n - cutProbLeft A * cutProbRight B| ≤
            |hiddenJoint A B n - hiddenProbLeft A * hiddenProbRight B|) :
    pom_multiplicity_composition_exponential_mixing_statement
      { CutEvent := CutEvent
        rate := rate
        cutProbLeft := cutProbLeft
        cutProbRight := cutProbRight
        cutJoint := cutJoint
        hiddenJoint := hiddenJoint
        hiddenProbLeft := hiddenProbLeft
        hiddenProbRight := hiddenProbRight
        mixingConstant := mixingConstant
        mixingConstant_nonneg := mixingConstant_nonneg
        hidden_exponential_mixing := hidden_exponential_mixing
        cut_edge_transfer := cut_edge_transfer } := by
  intro A B
  refine ⟨mixingConstant_nonneg A B, ?_⟩
  intro n
  exact le_trans (cut_edge_transfer A B n) (hidden_exponential_mixing A B n)

end Omega.POM
