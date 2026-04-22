import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

noncomputable section

section

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Total squared block norm of a finite pure state. -/
def conclusion_fold_quantum_projective_simplex_quotient_totalWeight (ψ : X → ℂ) : ℝ :=
  ∑ x, Complex.normSq (ψ x)

/-- The classical probability vector attached to a nonzero pure state. -/
def conclusion_fold_quantum_projective_simplex_quotient_probability (ψ : X → ℂ) : X → ℝ :=
  fun x => Complex.normSq (ψ x) /
    conclusion_fold_quantum_projective_simplex_quotient_totalWeight ψ

/-- A concrete finite simplex point. -/
def conclusion_fold_quantum_projective_simplex_quotient_simplexPoint (p : X → ℝ) : Prop :=
  (∀ x, 0 ≤ p x) ∧ (∑ x, p x) = 1

/-- Blockwise phase action on one-dimensional blocks. -/
def conclusion_fold_quantum_projective_simplex_quotient_phaseAction (u : X → ℂ) (ψ : X → ℂ) :
    X → ℂ :=
  fun x => u x * ψ x

/-- Two normalized pure states are equivalent when they differ by blockwise phases. -/
def conclusion_fold_quantum_projective_simplex_quotient_phaseEquivalent
    (ψ φ : X → ℂ) : Prop :=
  ∃ u : X → ℂ,
    (∀ x, Complex.normSq (u x) = 1) ∧
      φ = conclusion_fold_quantum_projective_simplex_quotient_phaseAction u ψ

/-- Canonical representative of a simplex point by nonnegative amplitudes. -/
def conclusion_fold_quantum_projective_simplex_quotient_representative (p : X → ℝ) : X → ℂ :=
  fun x => (Real.sqrt (p x) : ℂ)

private lemma conclusion_fold_quantum_projective_simplex_quotient_totalWeight_phaseAction
    (u ψ : X → ℂ) (hu : ∀ x, Complex.normSq (u x) = 1) :
    conclusion_fold_quantum_projective_simplex_quotient_totalWeight
        (conclusion_fold_quantum_projective_simplex_quotient_phaseAction u ψ) =
      conclusion_fold_quantum_projective_simplex_quotient_totalWeight ψ := by
  simp [conclusion_fold_quantum_projective_simplex_quotient_totalWeight,
    conclusion_fold_quantum_projective_simplex_quotient_phaseAction, Complex.normSq_mul, hu]

private lemma conclusion_fold_quantum_projective_simplex_quotient_totalWeight_representative
    (p : X → ℝ) (hp : conclusion_fold_quantum_projective_simplex_quotient_simplexPoint p) :
    conclusion_fold_quantum_projective_simplex_quotient_totalWeight
        (conclusion_fold_quantum_projective_simplex_quotient_representative p) = 1 := by
  rcases hp with ⟨hp_nonneg, hp_sum⟩
  calc
    conclusion_fold_quantum_projective_simplex_quotient_totalWeight
        (conclusion_fold_quantum_projective_simplex_quotient_representative p)
      = ∑ x, p x := by
          simp [conclusion_fold_quantum_projective_simplex_quotient_totalWeight,
            conclusion_fold_quantum_projective_simplex_quotient_representative, hp_nonneg,
            Complex.normSq_apply, Real.sq_sqrt]
    _ = 1 := hp_sum

private lemma conclusion_fold_quantum_projective_simplex_quotient_probability_phaseAction
    (u ψ : X → ℂ) (hu : ∀ x, Complex.normSq (u x) = 1) :
    conclusion_fold_quantum_projective_simplex_quotient_probability
        (conclusion_fold_quantum_projective_simplex_quotient_phaseAction u ψ) =
      conclusion_fold_quantum_projective_simplex_quotient_probability ψ := by
  ext x
  simp [conclusion_fold_quantum_projective_simplex_quotient_probability,
    conclusion_fold_quantum_projective_simplex_quotient_phaseAction,
    conclusion_fold_quantum_projective_simplex_quotient_totalWeight_phaseAction, hu,
    Complex.normSq_mul]

private lemma conclusion_fold_quantum_projective_simplex_quotient_probability_scaling
    (c : ℂ) (ψ : X → ℂ)
    (hc : c ≠ 0)
    (hψ :
      conclusion_fold_quantum_projective_simplex_quotient_totalWeight ψ ≠ 0) :
    conclusion_fold_quantum_projective_simplex_quotient_probability (fun x => c * ψ x) =
      conclusion_fold_quantum_projective_simplex_quotient_probability ψ := by
  have hc0 : Complex.normSq c ≠ 0 := by
    intro h0
    exact hc (Complex.normSq_eq_zero.mp h0)
  have htotal :
      conclusion_fold_quantum_projective_simplex_quotient_totalWeight (fun x => c * ψ x) =
        Complex.normSq c *
          conclusion_fold_quantum_projective_simplex_quotient_totalWeight ψ := by
    simp [conclusion_fold_quantum_projective_simplex_quotient_totalWeight, Complex.normSq_mul,
      Finset.mul_sum]
  ext x
  rw [conclusion_fold_quantum_projective_simplex_quotient_probability,
    conclusion_fold_quantum_projective_simplex_quotient_probability, htotal, Complex.normSq_mul]
  field_simp [hc0, hψ]

private lemma conclusion_fold_quantum_projective_simplex_quotient_probability_representative
    (p : X → ℝ) (hp : conclusion_fold_quantum_projective_simplex_quotient_simplexPoint p) :
    conclusion_fold_quantum_projective_simplex_quotient_probability
        (conclusion_fold_quantum_projective_simplex_quotient_representative p) = p := by
  rcases hp with ⟨hp_nonneg, hp_sum⟩
  ext x
  rw [conclusion_fold_quantum_projective_simplex_quotient_probability,
    conclusion_fold_quantum_projective_simplex_quotient_totalWeight_representative p
      ⟨hp_nonneg, hp_sum⟩, div_one]
  simp [conclusion_fold_quantum_projective_simplex_quotient_representative, hp_nonneg,
    Complex.normSq_apply, Real.sq_sqrt]

/-- Paper label: `prop:conclusion-fold-quantum-projective-simplex-quotient`.
On normalized finite pure states with one-dimensional visible blocks, the projective quotient by
blockwise phases is exactly the simplex of squared block norms. -/
theorem paper_conclusion_fold_quantum_projective_simplex_quotient :
    (∀ (c : ℂ) (ψ : X → ℂ),
      c ≠ 0 →
        conclusion_fold_quantum_projective_simplex_quotient_totalWeight ψ ≠ 0 →
          conclusion_fold_quantum_projective_simplex_quotient_probability (fun x => c * ψ x) =
            conclusion_fold_quantum_projective_simplex_quotient_probability ψ) ∧
      (∀ (u ψ : X → ℂ), (∀ x, Complex.normSq (u x) = 1) →
        conclusion_fold_quantum_projective_simplex_quotient_probability
            (conclusion_fold_quantum_projective_simplex_quotient_phaseAction u ψ) =
          conclusion_fold_quantum_projective_simplex_quotient_probability ψ) ∧
      (∀ p : X → ℝ,
        conclusion_fold_quantum_projective_simplex_quotient_simplexPoint p →
          ∃ ψ : X → ℂ,
            conclusion_fold_quantum_projective_simplex_quotient_totalWeight ψ = 1 ∧
              conclusion_fold_quantum_projective_simplex_quotient_probability ψ = p) ∧
      (∀ ψ φ : X → ℂ,
        conclusion_fold_quantum_projective_simplex_quotient_totalWeight ψ = 1 →
          conclusion_fold_quantum_projective_simplex_quotient_totalWeight φ = 1 →
            (conclusion_fold_quantum_projective_simplex_quotient_phaseEquivalent ψ φ ↔
              conclusion_fold_quantum_projective_simplex_quotient_probability ψ =
                conclusion_fold_quantum_projective_simplex_quotient_probability φ)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c ψ hc hψ
    exact conclusion_fold_quantum_projective_simplex_quotient_probability_scaling c ψ hc hψ
  · intro u ψ hu
    exact conclusion_fold_quantum_projective_simplex_quotient_probability_phaseAction u ψ hu
  · intro p hp
    refine ⟨conclusion_fold_quantum_projective_simplex_quotient_representative p, ?_, ?_⟩
    · exact conclusion_fold_quantum_projective_simplex_quotient_totalWeight_representative p hp
    · exact conclusion_fold_quantum_projective_simplex_quotient_probability_representative p hp
  · intro ψ φ hψ hφ
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact (conclusion_fold_quantum_projective_simplex_quotient_probability_phaseAction u ψ hu).symm
    · intro hprob
      have hnorm :
          ∀ x, Complex.normSq (ψ x) = Complex.normSq (φ x) := by
        intro x
        have hx := congrArg (fun q : X → ℝ => q x) hprob
        simpa [conclusion_fold_quantum_projective_simplex_quotient_probability, hψ, hφ] using hx
      let u : X → ℂ := fun x =>
        if hzero : ψ x = 0 then 1 else φ x / ψ x
      refine ⟨u, ?_, ?_⟩
      · intro x
        by_cases hzero : ψ x = 0
        · simp [u, hzero]
        · have hnormx := hnorm x
          have hψ0 : Complex.normSq (ψ x) ≠ 0 := by
            intro h0
            exact hzero (Complex.normSq_eq_zero.mp h0)
          have hφ0 : φ x ≠ 0 := by
            intro hφzero
            apply hψ0
            rw [hnormx, hφzero]
            simp
          calc
            Complex.normSq (u x) = Complex.normSq (φ x / ψ x) := by simp [u, hzero]
            _ = Complex.normSq (φ x) / Complex.normSq (ψ x) := by
                  rw [Complex.normSq_div]
            _ = 1 := by rw [← hnormx, div_self hψ0]
      · ext x
        by_cases hzero : ψ x = 0
        · have hφzero : φ x = 0 := by
            apply Complex.normSq_eq_zero.mp
            rw [← hnorm x, hzero]
            simp
          simp [u, conclusion_fold_quantum_projective_simplex_quotient_phaseAction, hzero, hφzero]
        · simp [u, conclusion_fold_quantum_projective_simplex_quotient_phaseAction, hzero,
            div_mul_cancel₀]

end

end

end Omega.Conclusion
