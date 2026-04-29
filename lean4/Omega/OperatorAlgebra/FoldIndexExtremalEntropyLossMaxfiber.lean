import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.OperatorAlgebra.FoldWatataniIndexMultiplicityField
import Omega.OperatorAlgebra.RenyiFlatnessSupEqualsLogIndex

namespace Omega.OperatorAlgebra

open FoldJonesBasicConstructionDirectsum

section

variable {Ω X : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω] [Fintype X] [DecidableEq X]

/-- The largest fold-fiber multiplicity. -/
def foldLargestFiberCard (fold : Ω → X) : ℕ :=
  Finset.univ.sup fun x => Fintype.card (foldFiber fold x)

/-- The index field achieves its maximum exactly at the largest fiber multiplicity. -/
def foldIndexEqualsMaxFiber (fold : Ω → X) : Prop :=
  (Finset.univ.sup fun x => foldWatataniIndexElement fold x) = foldLargestFiberCard fold

/-- The point-mass coarse-graining loss is the logarithm of the visible fiber size. -/
def foldPointMassLossFormula (fold : Ω → X) : Prop :=
  ∀ ω, foldFiberRenyiFlatness fold ω = Real.log (Fintype.card (foldFiber fold (fold ω)))

/-- The worst point-mass loss is realized exactly on the largest fibers. -/
def foldMaxLossCharacterization (fold : Ω → X) : Prop :=
  sSup (Set.range (foldFiberRenyiFlatness fold)) = Real.log (foldLargestFiberCard fold) ∧
    ∀ ω, foldFiberRenyiFlatness fold ω = Real.log (foldLargestFiberCard fold) ↔
      Fintype.card (foldFiber fold (fold ω)) = foldLargestFiberCard fold

private lemma foldFiber_card_pos_at_point (fold : Ω → X) (ω : Ω) :
    0 < Fintype.card (foldFiber fold (fold ω)) := by
  simpa using (Fintype.card_pos_iff.mpr ⟨⟨ω, rfl⟩⟩)

private lemma exists_point_attaining_foldLargestFiberCard (fold : Ω → X)
    (hfold : Function.Surjective fold) :
    ∃ ω, Fintype.card (foldFiber fold (fold ω)) = foldLargestFiberCard fold := by
  classical
  letI : Nonempty X := ⟨fold (Classical.choice ‹Nonempty Ω›)⟩
  obtain ⟨x, -, hx⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset X) Finset.univ_nonempty
    (fun x => Fintype.card (foldFiber fold x))
  rcases hfold x with ⟨ω, rfl⟩
  exact ⟨ω, by simpa [foldLargestFiberCard] using hx.symm⟩

/-- Paper label: `prop:op-algebra-index-extremal-entropy-loss-maxfiber`.
For a finite surjective fold map, the Watatani index field has maximum equal to the largest fiber
multiplicity, the point-mass entropy loss is the logarithmic fiber size, and the maximizers are
exactly the points lying in a largest fiber. -/
theorem paper_op_algebra_index_extremal_entropy_loss_maxfiber (fold : Ω → X)
    (hfold : Function.Surjective fold) :
    foldIndexEqualsMaxFiber fold ∧ foldPointMassLossFormula fold ∧
      foldMaxLossCharacterization fold := by
  classical
  have hcap : ∀ ω, Fintype.card (foldFiber fold (fold ω)) ≤ foldLargestFiberCard fold := by
    intro ω
    exact Finset.le_sup (f := fun x : X => Fintype.card (foldFiber fold x)) (Finset.mem_univ _)
  have hext : ∃ ω, Fintype.card (foldFiber fold (fold ω)) = foldLargestFiberCard fold :=
    exists_point_attaining_foldLargestFiberCard fold hfold
  refine ⟨?_, ?_, ?_⟩
  · simp [foldIndexEqualsMaxFiber, foldLargestFiberCard, foldWatataniIndexElement,
      foldWatataniIndexCoefficient]
  · intro ω
    rfl
  · refine ⟨?_, ?_⟩
    · exact paper_op_algebra_renyi_flatness_sup_equals_log_index fold (foldLargestFiberCard fold)
        hcap hext
    · intro ω
      constructor
      · intro hω
        rcases hext with ⟨ωmax, hωmax⟩
        have hωpos : 0 < (Fintype.card (foldFiber fold (fold ω)) : ℝ) := by
          exact_mod_cast foldFiber_card_pos_at_point fold ω
        have hmaxpos : 0 < (foldLargestFiberCard fold : ℝ) := by
          have hωmaxpos : 0 < (Fintype.card (foldFiber fold (fold ωmax)) : ℝ) := by
            exact_mod_cast foldFiber_card_pos_at_point fold ωmax
          simpa [hωmax] using hωmaxpos
        have hcast : (Fintype.card (foldFiber fold (fold ω)) : ℝ) = foldLargestFiberCard fold := by
          apply Real.exp_injective
          simpa [foldFiberRenyiFlatness, Real.exp_log hωpos, Real.exp_log hmaxpos] using
            congrArg Real.exp hω
        exact_mod_cast hcast
      · intro hω
        simp [foldFiberRenyiFlatness, hω]

end

end Omega.OperatorAlgebra
