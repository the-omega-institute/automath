import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Omega.OperatorAlgebra.FoldDmaxCapacityEqualsLogIndex
import Omega.OperatorAlgebra.FoldIndexExtremalEntropyLossMaxfiber

namespace Omega.OperatorAlgebra

open FoldJonesBasicConstructionDirectsum

section

variable {Ω X : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω] [Fintype X] [DecidableEq X]

omit [DecidableEq Ω] in
private lemma exists_point_attaining_foldLargestFiberCard (fold : Ω → X)
    (hfold : Function.Surjective fold) :
    ∃ ω, Fintype.card (foldFiber fold (fold ω)) = foldLargestFiberCard fold := by
  classical
  letI : Nonempty X := ⟨fold (Classical.choice ‹Nonempty Ω›)⟩
  obtain ⟨x, -, hx⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset X) Finset.univ_nonempty
    (fun x => Fintype.card (foldFiber fold x))
  rcases hfold x with ⟨ω, rfl⟩
  exact ⟨ω, by simpa [foldLargestFiberCard] using hx.symm⟩

/-- Paper label: `cor:op-algebra-commutative-dmax-extremizers-maxfiber`.
In the finite commutative fold model, the `Dmax` endpoint is the logarithm of the largest fiber
size, every point mass is bounded by that value, and the extremizers are exactly the point masses
supported on maximal fibers. -/
theorem paper_op_algebra_commutative_dmax_extremizers_maxfiber (fold : Ω → X)
    (hfold : Function.Surjective fold) :
    foldDmaxCapacity fold = Real.log (foldLargestFiberCard fold) ∧
      (∀ ω, foldFiberRenyiFlatness fold ω ≤ foldDmaxCapacity fold) ∧
      (∀ ω, foldFiberRenyiFlatness fold ω = foldDmaxCapacity fold ↔
        Fintype.card (foldFiber fold (fold ω)) = foldLargestFiberCard fold) ∧
      ∃ ω, foldFiberRenyiFlatness fold ω = foldDmaxCapacity fold := by
  have hdmax := paper_op_algebra_dmax_capacity_equals_log_index fold hfold
  have hmax := paper_op_algebra_index_extremal_entropy_loss_maxfiber fold hfold
  rcases hdmax with ⟨hbound, hdmax_eq⟩
  rcases hmax with ⟨_, _, hchar⟩
  refine ⟨hdmax_eq, ?_, ?_, ?_⟩
  · intro ω
    rw [hdmax_eq]
    exact hbound ω
  · intro ω
    rw [hdmax_eq]
    exact hchar.2 ω
  · rcases exists_point_attaining_foldLargestFiberCard fold hfold with ⟨ω, hω⟩
    refine ⟨ω, ?_⟩
    rw [hdmax_eq]
    exact (hchar.2 ω).2 hω

end

end Omega.OperatorAlgebra
