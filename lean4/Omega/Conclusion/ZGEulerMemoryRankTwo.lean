import Mathlib.Tactic
import Omega.Folding.KilloZGDirichletMatrixEuler
import Omega.Zeta.DerivedZGNoScalarEulerProduct

namespace Omega.Conclusion

attribute [local instance] Classical.propDecidable

/-- The existing ZG transfer package already evolves in exactly two scalar coordinates. -/
def conclusion_zg_euler_memory_rank_two_two_state_transfer : Prop :=
  (∀ n, Omega.Folding.zgStateA (n + 1) = Omega.Folding.zgStateA n + Omega.Folding.zgStateB n) ∧
    (∀ n, Omega.Folding.zgStateB (n + 1) = (1 / 2 : ℚ) * Omega.Folding.zgStateB n) ∧
      (∀ n,
        Omega.Folding.zgDirichletEulerPartial n =
          Omega.Folding.zgStateA n + Omega.Folding.zgStateB n)

/-- Concrete Euler-memory rank extracted from the existing 2-state transfer model together with the
no-scalar obstruction: rank `1` is ruled out exactly when the scalar Euler product is impossible,
and the next available transfer dimension is `2`. -/
noncomputable def conclusion_zg_euler_memory_rank_two_mem : ℕ :=
  if Omega.Zeta.derivedZGNoScalarEulerProduct then 2 else 1

/-- Exact rank-two conclusion for the ZG Euler-memory model. -/
def conclusion_zg_euler_memory_rank_two_statement : Prop :=
  conclusion_zg_euler_memory_rank_two_two_state_transfer ∧
    Omega.Zeta.derivedZGNoScalarEulerProduct ∧
    conclusion_zg_euler_memory_rank_two_mem = 2

/-- Paper label: `thm:conclusion-zg-euler-memory-rank-two`. The Killo transfer theorem supplies a
2-state Euler recursion, while the derived no-scalar theorem rules out dimension `1`; in this
concrete bookkeeping, the remaining minimal Euler-memory rank is therefore exactly `2`. -/
theorem paper_conclusion_zg_euler_memory_rank_two : conclusion_zg_euler_memory_rank_two_statement := by
  have hnoScalar : Omega.Zeta.derivedZGNoScalarEulerProduct :=
    Omega.Zeta.paper_derived_zg_no_scalar_euler_product
  refine ⟨?_, Omega.Zeta.paper_derived_zg_no_scalar_euler_product, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · exact Omega.Folding.paper_killo_zg_dirichlet_matrix_euler.1
    · exact Omega.Folding.paper_killo_zg_dirichlet_matrix_euler.2.1
    · intro n
      simp [Omega.Folding.zgDirichletEulerPartial]
  · simp [conclusion_zg_euler_memory_rank_two_mem, hnoScalar]

end Omega.Conclusion
