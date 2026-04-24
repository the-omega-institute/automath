import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Omega.OperatorAlgebra.FoldWatataniIndexMultiplicityField

namespace Omega.OperatorAlgebra

open FoldJonesBasicConstructionDirectsum

section

variable {Ω X : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype X] [DecidableEq X]

/-- Fiberwise finite-model proxy for the worst Rényi flatness at the point `ω`. -/
noncomputable def foldFiberRenyiFlatness (fold : Ω → X) (ω : Ω) : ℝ :=
  Real.log (Fintype.card (foldFiber fold (fold ω)))

private lemma foldFiber_card_pos (fold : Ω → X) (ω : Ω) :
    0 < Fintype.card (foldFiber fold (fold ω)) := by
  simpa using (Fintype.card_pos_iff.mpr ⟨⟨ω, rfl⟩⟩)

private lemma foldFiberRenyiFlatness_le_log_index
    (fold : Ω → X) (Ind : ℕ)
    (hcap : ∀ ω, Fintype.card (foldFiber fold (fold ω)) ≤ Ind) :
    ∀ ω, foldFiberRenyiFlatness fold ω ≤ Real.log Ind := by
  intro ω
  unfold foldFiberRenyiFlatness
  have hωpos : 0 < (Fintype.card (foldFiber fold (fold ω)) : ℝ) := by
    exact_mod_cast foldFiber_card_pos fold ω
  exact Real.log_le_log hωpos (by exact_mod_cast hcap ω)

/-- Paper label: `cor:op-algebra-renyi-flatness-sup-equals-log-index`.
If every accessible fiber has size at most `Ind(E)` and one fiber attains that size, then the
finite-model Rényi-flatness supremum is exactly `log Ind(E)`. -/
theorem paper_op_algebra_renyi_flatness_sup_equals_log_index
    (fold : Ω → X) (Ind : ℕ)
    (hcap : ∀ ω, Fintype.card (foldFiber fold (fold ω)) ≤ Ind)
    (hext : ∃ ω, Fintype.card (foldFiber fold (fold ω)) = Ind) :
    sSup (Set.range (foldFiberRenyiFlatness fold)) = Real.log Ind := by
  rcases hext with ⟨ω0, hω0⟩
  have hupper := foldFiberRenyiFlatness_le_log_index fold Ind hcap
  have hnonempty : (Set.range (foldFiberRenyiFlatness fold)).Nonempty := ⟨_, ⟨ω0, rfl⟩⟩
  have hbdd : BddAbove (Set.range (foldFiberRenyiFlatness fold)) := by
    refine ⟨Real.log Ind, ?_⟩
    rintro _ ⟨ω, rfl⟩
    exact hupper ω
  have hsSup_le : sSup (Set.range (foldFiberRenyiFlatness fold)) ≤ Real.log Ind := by
    exact csSup_le hnonempty (by rintro _ ⟨ω, rfl⟩; exact hupper ω)
  have hlog_mem : Real.log Ind ∈ Set.range (foldFiberRenyiFlatness fold) := by
    refine ⟨ω0, ?_⟩
    simp [foldFiberRenyiFlatness, hω0]
  have hlog_le : Real.log Ind ≤ sSup (Set.range (foldFiberRenyiFlatness fold)) := by
    exact le_csSup hbdd hlog_mem
  exact le_antisymm hsSup_le hlog_le

end

end Omega.OperatorAlgebra
