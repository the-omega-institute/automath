import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

noncomputable section

/-- The concrete two-point angular support on the unit circle. -/
def conclusion_angular_residue_measure_reconstruction_support_point (i : Fin 2) : ℂ :=
  if i = 0 then 1 else -1

/-- The Fourier coefficient of the two-atom angular residue measure. -/
def conclusion_angular_residue_measure_reconstruction_fourier
    (weights : Fin 2 → ℂ) (k : ℕ) : ℂ :=
  ∑ i, weights i * conclusion_angular_residue_measure_reconstruction_support_point i ^ k

/-- The wallcrossing jump normalized by the radial factor `t^k`. -/
def conclusion_angular_residue_measure_reconstruction_jump
    (t : ℝ) (weights : Fin 2 → ℂ) (k : ℕ) : ℂ :=
  conclusion_angular_residue_measure_reconstruction_fourier weights k / (t : ℂ) ^ k

private lemma conclusion_angular_residue_measure_reconstruction_fourier_zero
    (weights : Fin 2 → ℂ) :
    conclusion_angular_residue_measure_reconstruction_fourier weights 0 =
      weights 0 + weights 1 := by
  unfold conclusion_angular_residue_measure_reconstruction_fourier
    conclusion_angular_residue_measure_reconstruction_support_point
  simp

private lemma conclusion_angular_residue_measure_reconstruction_fourier_one
    (weights : Fin 2 → ℂ) :
    conclusion_angular_residue_measure_reconstruction_fourier weights 1 =
      weights 0 - weights 1 := by
  unfold conclusion_angular_residue_measure_reconstruction_fourier
    conclusion_angular_residue_measure_reconstruction_support_point
  simp
  ring

private lemma conclusion_angular_residue_measure_reconstruction_weights_from_fourier
    (weights : Fin 2 → ℂ) :
    weights 0 =
      (conclusion_angular_residue_measure_reconstruction_fourier weights 0 +
          conclusion_angular_residue_measure_reconstruction_fourier weights 1) / 2 ∧
      weights 1 =
        (conclusion_angular_residue_measure_reconstruction_fourier weights 0 -
            conclusion_angular_residue_measure_reconstruction_fourier weights 1) / 2 := by
  rw [conclusion_angular_residue_measure_reconstruction_fourier_zero,
    conclusion_angular_residue_measure_reconstruction_fourier_one]
  constructor <;> ring

private lemma conclusion_angular_residue_measure_reconstruction_eq_of_fourier_eq
    {weights₁ weights₂ : Fin 2 → ℂ}
    (h0 :
      conclusion_angular_residue_measure_reconstruction_fourier weights₁ 0 =
        conclusion_angular_residue_measure_reconstruction_fourier weights₂ 0)
    (h1 :
      conclusion_angular_residue_measure_reconstruction_fourier weights₁ 1 =
        conclusion_angular_residue_measure_reconstruction_fourier weights₂ 1) :
    weights₁ = weights₂ := by
  funext i
  fin_cases i
  · rcases conclusion_angular_residue_measure_reconstruction_weights_from_fourier weights₁ with
      ⟨h₁zero, _⟩
    rcases conclusion_angular_residue_measure_reconstruction_weights_from_fourier weights₂ with
      ⟨h₂zero, _⟩
    change weights₁ 0 = weights₂ 0
    rw [h₁zero, h₂zero, h0, h1]
  · rcases conclusion_angular_residue_measure_reconstruction_weights_from_fourier weights₁ with
      ⟨_, h₁one⟩
    rcases conclusion_angular_residue_measure_reconstruction_weights_from_fourier weights₂ with
      ⟨_, h₂one⟩
    change weights₁ 1 = weights₂ 1
    rw [h₁one, h₂one, h0, h1]

/-- Paper label: `cor:conclusion-angular-residue-measure-reconstruction`. In the concrete
two-atom unit-circle model, the normalized wallcrossing jumps are exactly the Fourier
coefficients divided by `t^k`, and equality of all jumps forces equality of the angular residue
weights. -/
theorem paper_conclusion_angular_residue_measure_reconstruction
    (t : ℝ) (ht : 1 < t) (weights : Fin 2 → ℂ) :
    (∀ k : ℕ,
      conclusion_angular_residue_measure_reconstruction_fourier weights k =
        (t : ℂ) ^ k * conclusion_angular_residue_measure_reconstruction_jump t weights k) ∧
      (∀ weights' : Fin 2 → ℂ,
        (∀ k : ℕ,
          conclusion_angular_residue_measure_reconstruction_jump t weights' k =
            conclusion_angular_residue_measure_reconstruction_jump t weights k) →
        weights' = weights) := by
  have ht0 : (t : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_trans zero_lt_one ht))
  refine ⟨?_, ?_⟩
  · intro k
    unfold conclusion_angular_residue_measure_reconstruction_jump
    field_simp [ht0]
  · intro weights' hjump
    have h0jump := hjump 0
    have h1jump := hjump 1
    have h0 :
        conclusion_angular_residue_measure_reconstruction_fourier weights' 0 =
          conclusion_angular_residue_measure_reconstruction_fourier weights 0 := by
      simpa [conclusion_angular_residue_measure_reconstruction_jump]
        using h0jump
    have h1 :
        conclusion_angular_residue_measure_reconstruction_fourier weights' 1 =
          conclusion_angular_residue_measure_reconstruction_fourier weights 1 := by
      have ht1 : (t : ℂ) ≠ 0 := ht0
      have hmul := congrArg (fun z => (t : ℂ) * z) h1jump
      simpa [conclusion_angular_residue_measure_reconstruction_jump, ht1] using hmul
    exact conclusion_angular_residue_measure_reconstruction_eq_of_fourier_eq h0 h1

end

end Omega.Conclusion
