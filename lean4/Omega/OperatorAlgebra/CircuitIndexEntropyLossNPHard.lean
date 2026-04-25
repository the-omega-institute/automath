import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.OperatorAlgebra.CircuitCondexpIndexMaxfiber
import Omega.OperatorAlgebra.CircuitNoninjectiveNPComplete

namespace Omega.OperatorAlgebra

open FoldJonesBasicConstructionDirectsum

/-- The Watatani index of the finite circuit conditional expectation, encoded as the supremum of
the blockwise index element. -/
def circuit_index_entropy_loss_np_hard_index {n : ℕ} (C : BoolCircuit n) : ℕ :=
  Finset.univ.sup (fun y => foldWatataniIndexElement C y)

/-- The additive error threshold separating `log 1 = 0` from `log 2`. -/
noncomputable def circuit_index_entropy_loss_np_hard_gap : ℝ :=
  Real.log 2 / 2

/-- Concrete hardness package for the SAT reduction circuit: any additive approximation to
`log Ind(E_C)` within error `< (log 2) / 2` decides satisfiability by thresholding at
`(log 2) / 2`. -/
def circuit_index_entropy_loss_np_hard_statement : Prop :=
  ∀ {n : ℕ} (φ : BitVec n → Bool) (q : ℝ),
    |q - Real.log (circuit_index_entropy_loss_np_hard_index (satReductionCircuit φ))| <
        circuit_index_entropy_loss_np_hard_gap →
      (q < circuit_index_entropy_loss_np_hard_gap ↔ ¬ satisfiable φ)

lemma circuit_index_entropy_loss_np_hard_no_collision_subsingleton
    {n : ℕ} {C : BoolCircuit n} (hNoCollision : ¬ circuitMaxFiberAtLeastTwo C) (y : BitVec n) :
    Subsingleton (foldFiber C y) := by
  refine Fintype.card_le_one_iff_subsingleton.mp ?_
  rw [Fintype.card_le_one_iff]
  intro a b
  by_cases hab : a.1 = b.1
  · cases a
    cases b
    simp_all
  · exfalso
    exact hNoCollision ⟨a.1, b.1, hab, a.2.trans b.2.symm⟩

lemma circuit_index_entropy_loss_np_hard_maxfiber_eq_one_of_not_satisfiable
    {n : ℕ} (φ : BitVec n → Bool) :
    ¬ satisfiable φ →
      circuit_index_entropy_loss_np_hard_index (satReductionCircuit φ) = 1 := by
  intro hUnsat
  let C : BoolCircuit (n + 1) := satReductionCircuit φ
  have hCollision :
      ¬ circuitMaxFiberAtLeastTwo C := by
    intro hC
    exact hUnsat (((paper_circuit_noninjective_np_complete).2 φ).mpr hC)
  have hIndexRaw :
      Finset.univ.sup (fun y => foldWatataniIndexElement C y) =
        Finset.univ.sup (fun y => Fintype.card (foldFiber C y)) := by
    simpa using paper_circuit_condexp_index_maxfiber C
  have hIndex :
      circuit_index_entropy_loss_np_hard_index C =
        Finset.univ.sup (fun y => Fintype.card (foldFiber C y)) := by
    simpa [circuit_index_entropy_loss_np_hard_index] using hIndexRaw
  refine le_antisymm ?_ ?_
  · have hBound :
        Finset.univ.sup (fun y : BitVec (n + 1) => Fintype.card (foldFiber C y)) ≤ 1 := by
      refine Finset.sup_le ?_
      intro y hy
      have hSub :
          Subsingleton (foldFiber C y) :=
        circuit_index_entropy_loss_np_hard_no_collision_subsingleton hCollision y
      exact Fintype.card_le_one_iff_subsingleton.mpr hSub
    simpa [circuit_index_entropy_loss_np_hard_index, C] using
      (show Finset.univ.sup (fun y : BitVec (n + 1) => foldWatataniIndexElement C y) ≤ 1 by
        rw [hIndexRaw]
        exact hBound)
  · rw [hIndex]
    let y0 : BitVec (n + 1) := C (circuitZero (n + 1))
    have hy0 : y0 ∈ (Finset.univ : Finset (BitVec (n + 1))) := by
      simp [y0]
    have hFiber :
        1 ≤ Fintype.card (foldFiber C y0) := by
      let a0 : foldFiber C y0 := ⟨circuitZero (n + 1), rfl⟩
      simpa using Fintype.card_pos_iff.mpr ⟨a0⟩
    exact le_trans hFiber <|
      Finset.le_sup (s := Finset.univ)
        (f := fun y : BitVec (n + 1) => Fintype.card (foldFiber C y))
        hy0

lemma circuit_index_entropy_loss_np_hard_maxfiber_ge_two_of_satisfiable
    {n : ℕ} (φ : BitVec n → Bool) :
    satisfiable φ →
      2 ≤ circuit_index_entropy_loss_np_hard_index (satReductionCircuit φ) := by
  intro hSat
  let C : BoolCircuit (n + 1) := satReductionCircuit φ
  have hCollision :
      circuitMaxFiberAtLeastTwo C := ((paper_circuit_noninjective_np_complete).2 φ).mp hSat
  have hIndex :
      circuit_index_entropy_loss_np_hard_index C =
        Finset.univ.sup (fun y => Fintype.card (foldFiber C y)) := by
    simpa [circuit_index_entropy_loss_np_hard_index] using paper_circuit_condexp_index_maxfiber C
  rcases hCollision with ⟨a, b, hab, habEq⟩
  let y : BitVec (n + 1) := C a
  have hy : y ∈ (Finset.univ : Finset (BitVec (n + 1))) := by
    simp [y]
  have hCard :
      2 ≤ Fintype.card (foldFiber C y) := by
    have hlt : 1 < Fintype.card (foldFiber C y) := by
      exact Fintype.one_lt_card_iff.mpr ⟨⟨a, rfl⟩, ⟨b, by
        dsimp [y]
        exact habEq.symm⟩, by
        intro hEq
        exact hab (Subtype.ext_iff.mp hEq)⟩
    exact Nat.succ_le_of_lt hlt
  rw [hIndex]
  exact le_trans hCard <|
    Finset.le_sup (s := Finset.univ)
      (f := fun y : BitVec (n + 1) => Fintype.card (foldFiber C y))
      hy

lemma circuit_index_entropy_loss_np_hard_log_lower_bound
    {n : ℕ} (φ : BitVec n → Bool) :
    satisfiable φ →
      Real.log 2 ≤ Real.log (circuit_index_entropy_loss_np_hard_index (satReductionCircuit φ)) := by
  intro hSat
  have hTwo :
      (2 : ℝ) ≤ circuit_index_entropy_loss_np_hard_index (satReductionCircuit φ) := by
    exact_mod_cast circuit_index_entropy_loss_np_hard_maxfiber_ge_two_of_satisfiable φ hSat
  exact Real.log_le_log (by norm_num) hTwo

/-- Paper label: `cor:circuit-index-entropy-loss-np-hard`. The max-fiber/index identity converts
the SAT reduction into an additive threshold test for `log Ind(E_C)`: unsatisfiable formulas give
index `1`, satisfiable formulas force index at least `2`, and any additive approximation with
error `< (log 2) / 2` separates the two cases. -/
theorem paper_circuit_index_entropy_loss_np_hard :
    circuit_index_entropy_loss_np_hard_statement := by
  intro n φ q hApprox
  let I : ℕ := circuit_index_entropy_loss_np_hard_index (satReductionCircuit φ)
  constructor
  · intro hq hSat
    have hLogLower :
        Real.log 2 ≤ Real.log I := by
      simpa [I] using circuit_index_entropy_loss_np_hard_log_lower_bound φ hSat
    have hApproxLower : Real.log I - circuit_index_entropy_loss_np_hard_gap < q := by
      have hLower := (abs_lt.mp hApprox).1
      linarith
    have hGapLe : circuit_index_entropy_loss_np_hard_gap ≤ Real.log I - circuit_index_entropy_loss_np_hard_gap := by
      dsimp [circuit_index_entropy_loss_np_hard_gap] at *
      linarith
    linarith
  · intro hUnsat
    have hI1 : I = 1 := by
      simpa [I] using
        circuit_index_entropy_loss_np_hard_maxfiber_eq_one_of_not_satisfiable φ hUnsat
    have hUpper : q - Real.log I < circuit_index_entropy_loss_np_hard_gap := (abs_lt.mp hApprox).2
    have hLogOne : Real.log I = 0 := by simp [hI1]
    dsimp [circuit_index_entropy_loss_np_hard_gap] at *
    linarith

end Omega.OperatorAlgebra
