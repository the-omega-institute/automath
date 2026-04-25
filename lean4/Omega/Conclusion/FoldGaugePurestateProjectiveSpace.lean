import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic
import Omega.Conclusion.FoldQuantumProjectiveSimplexQuotient

namespace Omega.Conclusion

noncomputable section

/-- The visible pure-state Hilbert space modeled by the finite carrier `X_m`. -/
abbrev conclusion_fold_gauge_purestate_projective_space_visible_space (m : Nat) :=
  Fin (Nat.fib (m + 2)) → ℂ

/-- Finite-dimensional bookkeeping proxy for `dim U_m`. -/
def conclusion_fold_gauge_purestate_projective_space_visible_dimension (m : Nat) : Nat :=
  Module.finrank ℂ (conclusion_fold_gauge_purestate_projective_space_visible_space m)

/-- Finite-dimensional bookkeeping proxy for `dim W_m = 2^m - |X_m|`. -/
def conclusion_fold_gauge_purestate_projective_space_hidden_dimension (m : Nat) : Nat :=
  2 ^ m - Nat.fib (m + 2)

/-- Wrapper around the projective-simplex quotient together with the visible/hidden dimension
bookkeeping and the concrete `m = 6` specialization. -/
def conclusion_fold_gauge_purestate_projective_space_statement (m : Nat) : Prop :=
  let X := Fin (Nat.fib (m + 2))
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
              conclusion_fold_quantum_projective_simplex_quotient_probability φ)) ∧
    conclusion_fold_gauge_purestate_projective_space_visible_dimension m = Nat.fib (m + 2) ∧
    conclusion_fold_gauge_purestate_projective_space_hidden_dimension m = 2 ^ m - Nat.fib (m + 2) ∧
    (m = 6 →
      Nat.fib (m + 2) = 21 ∧
        conclusion_fold_gauge_purestate_projective_space_visible_dimension m = 21 ∧
        conclusion_fold_gauge_purestate_projective_space_hidden_dimension m = 43)

/-- Paper label: `cor:conclusion-fold-gauge-purestate-projective-space`. -/
theorem paper_conclusion_fold_gauge_purestate_projective_space (m : Nat) :
    conclusion_fold_gauge_purestate_projective_space_statement m := by
  dsimp [conclusion_fold_gauge_purestate_projective_space_statement]
  refine ⟨?_, ?_, ?_, ?_, ?_, rfl, ?_⟩
  · simpa using
      (paper_conclusion_fold_quantum_projective_simplex_quotient (X := Fin (Nat.fib (m + 2)))).1
  · simpa using
      (paper_conclusion_fold_quantum_projective_simplex_quotient (X := Fin (Nat.fib (m + 2)))).2.1
  · simpa using
      (paper_conclusion_fold_quantum_projective_simplex_quotient (X := Fin (Nat.fib (m + 2)))).2.2.1
  · simpa using
      (paper_conclusion_fold_quantum_projective_simplex_quotient (X := Fin (Nat.fib (m + 2)))).2.2.2
  · simpa [conclusion_fold_gauge_purestate_projective_space_visible_dimension,
      conclusion_fold_gauge_purestate_projective_space_visible_space] using
      (Module.finrank_fin_fun (R := ℂ) (n := Nat.fib (m + 2)))
  · intro hm
    subst hm
    have hFib : Nat.fib 8 = 21 := by decide
    have hFib' : Nat.fib (6 + 2) = 21 := by simpa using hFib
    have hVisible : conclusion_fold_gauge_purestate_projective_space_visible_dimension 6 = 21 := by
      unfold conclusion_fold_gauge_purestate_projective_space_visible_dimension
      change Module.finrank ℂ (Fin (Nat.fib 8) → ℂ) = 21
      rw [hFib]
      simpa using
        (Module.finrank_fin_fun (R := ℂ) (n := 21))
    have hHidden : conclusion_fold_gauge_purestate_projective_space_hidden_dimension 6 = 43 := by
      norm_num [conclusion_fold_gauge_purestate_projective_space_hidden_dimension, hFib]
    exact ⟨hFib', hVisible, hHidden⟩

end

end Omega.Conclusion
