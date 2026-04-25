import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
import Omega.OperatorAlgebra.CircuitS2SharpPComplete
import Omega.SPG.PolytimeCompleteInvariantImpliesPEqualsNP

namespace Omega.OperatorAlgebra

open scoped BigOperators

/-- Concrete Boolean formulas packaged with their input arity. -/
abbrev universal_compilable_collision_kernel_implies_p_np_formula := Σ n : ℕ, BitVec n → Bool

/-- Chapter-local `UNSAT` predicate on the packaged Boolean formulas. -/
def universal_compilable_collision_kernel_implies_p_np_unsat
    (F : universal_compilable_collision_kernel_implies_p_np_formula) : Prop :=
  ¬ satisfiable F.2

/-- The compiled collision-kernel evaluation `uᵀ A^T v`. -/
noncomputable def universal_compilable_collision_kernel_implies_p_np_compiled_value
    (compileDim : ℕ → ℕ)
    (compileMatrix :
      ∀ F : universal_compilable_collision_kernel_implies_p_np_formula,
        Matrix (Fin (compileDim F.1)) (Fin (compileDim F.1)) ℕ)
    (compileLeft compileRight :
      ∀ F : universal_compilable_collision_kernel_implies_p_np_formula,
        Fin (compileDim F.1) → ℕ)
    (steps : ℕ → ℕ) (F : universal_compilable_collision_kernel_implies_p_np_formula) : ℕ :=
  ∑ i : Fin (compileDim F.1),
    compileLeft F i *
      ∑ j : Fin (compileDim F.1), ((compileMatrix F) ^ steps F.1) i j * compileRight F j

/-- The universal compilation hypothesis specialized to the concrete `S₂` reduction value. -/
def universal_compilable_collision_kernel_implies_p_np_compilation_hypothesis
    (compileDim : ℕ → ℕ)
    (compileMatrix :
      ∀ F : universal_compilable_collision_kernel_implies_p_np_formula,
        Matrix (Fin (compileDim F.1)) (Fin (compileDim F.1)) ℕ)
    (compileLeft compileRight :
      ∀ F : universal_compilable_collision_kernel_implies_p_np_formula,
        Fin (compileDim F.1) → ℕ)
    (steps : ℕ → ℕ) : Prop :=
  ∀ F,
    universal_compilable_collision_kernel_implies_p_np_compiled_value
        compileDim compileMatrix compileLeft compileRight steps F =
      circuit_s2_sharpp_complete_reductionValue 2 F.2

/-- Threshold classifier: the compiled `S₂` value equals the ambient identity contribution exactly
in the unsatisfiable case. -/
noncomputable def universal_compilable_collision_kernel_implies_p_np_decide_unsat
    (compileDim : ℕ → ℕ)
    (compileMatrix :
      ∀ F : universal_compilable_collision_kernel_implies_p_np_formula,
        Matrix (Fin (compileDim F.1)) (Fin (compileDim F.1)) ℕ)
    (compileLeft compileRight :
      ∀ F : universal_compilable_collision_kernel_implies_p_np_formula,
        Fin (compileDim F.1) → ℕ)
    (steps : ℕ → ℕ) (F : universal_compilable_collision_kernel_implies_p_np_formula) : Bool :=
  decide
    (universal_compilable_collision_kernel_implies_p_np_compiled_value
        compileDim compileMatrix compileLeft compileRight steps F =
      2 ^ (F.1 + 1))

private lemma universal_compilable_collision_kernel_implies_p_np_satCount_eq_zero_iff_not_satisfiable
    {n : ℕ} (φ : BitVec n → Bool) :
    circuit_s2_sharpp_complete_satCount φ = 0 ↔ ¬ satisfiable φ := by
  constructor
  · intro hCount hSat
    rcases hSat with ⟨w, hw⟩
    have hpos : 0 < circuit_s2_sharpp_complete_satCount φ := by
      unfold circuit_s2_sharpp_complete_satCount
      exact Fintype.card_pos_iff.mpr ⟨⟨w, hw⟩⟩
    omega
  · intro hUnsat
    classical
    unfold circuit_s2_sharpp_complete_satCount
    letI : IsEmpty {u : BitVec n // φ u = true} := ⟨fun w => hUnsat ⟨w.1, w.2⟩⟩
    simp

private lemma universal_compilable_collision_kernel_implies_p_np_parameter_ge_two_of_satisfiable
    {n : ℕ} (φ : BitVec n → Bool) (hSat : satisfiable φ) :
    2 ≤ circuit_s2_sharpp_complete_parameter φ := by
  have hpos : 0 < circuit_s2_sharpp_complete_satCount φ := by
    rcases hSat with ⟨w, hw⟩
    unfold circuit_s2_sharpp_complete_satCount
    exact Fintype.card_pos_iff.mpr ⟨⟨w, hw⟩⟩
  unfold circuit_s2_sharpp_complete_parameter
  cases hzero : liftedSatFormula φ (circuitZero (n + 1)) <;> omega

private lemma universal_compilable_collision_kernel_implies_p_np_ambient_lt_collision_value
    (N p : ℕ) (hp : 2 ≤ p) :
    N < p ^ 2 + (N - p) := by
  by_cases hpLe : p ≤ N
  · rw [pow_two]
    have hdecomp : N = (N - p) + p := by
      exact (Nat.sub_eq_iff_eq_add hpLe).1 rfl
    have hpSq : p < p * p := by
      nlinarith
    calc
      N = (N - p) + p := hdecomp
      _ < (N - p) + p * p := Nat.add_lt_add_left hpSq (N - p)
      _ = p * p + (N - p) := by omega
  · have hNp : N < p := lt_of_not_ge hpLe
    have hpSq : p < p ^ 2 := by
      rw [pow_two]
      nlinarith
    exact lt_of_lt_of_le (lt_trans hNp hpSq) (Nat.le_add_right _ _)

private lemma
    universal_compilable_collision_kernel_implies_p_np_reductionValue_eq_ambient_iff_not_satisfiable
    {n : ℕ} (φ : BitVec n → Bool) :
    circuit_s2_sharpp_complete_reductionValue 2 φ = 2 ^ (n + 1) ↔ ¬ satisfiable φ := by
  constructor
  · intro hEq hSat
    have hcountPos : 0 < circuit_s2_sharpp_complete_satCount φ := by
      rcases hSat with ⟨w, hw⟩
      unfold circuit_s2_sharpp_complete_satCount
      exact Fintype.card_pos_iff.mpr ⟨⟨w, hw⟩⟩
    have hgt : 2 ^ (n + 1) < circuit_s2_sharpp_complete_reductionValue 2 φ := by
      unfold circuit_s2_sharpp_complete_reductionValue circuit_s2_sharpp_complete_parameter
      cases hzero : liftedSatFormula φ (circuitZero (n + 1))
      ·
        have hp : 2 ≤ 2 * circuit_s2_sharpp_complete_satCount φ + 1 := by omega
        simpa [hzero] using
          universal_compilable_collision_kernel_implies_p_np_ambient_lt_collision_value
            (2 ^ (n + 1)) (2 * circuit_s2_sharpp_complete_satCount φ + 1) hp
      ·
        have hp : 2 ≤ 2 * circuit_s2_sharpp_complete_satCount φ := by omega
        simpa [hzero] using
          universal_compilable_collision_kernel_implies_p_np_ambient_lt_collision_value
            (2 ^ (n + 1)) (2 * circuit_s2_sharpp_complete_satCount φ) hp
    exact (Nat.ne_of_lt hgt) hEq.symm
  · intro hUnsat
    have hcount :
        circuit_s2_sharpp_complete_satCount φ = 0 := by
      exact
        (universal_compilable_collision_kernel_implies_p_np_satCount_eq_zero_iff_not_satisfiable
          φ).2 hUnsat
    have hzero : liftedSatFormula φ (circuitZero (n + 1)) = false := by
      cases hBool : liftedSatFormula φ (circuitZero (n + 1)) <;> simp
      have hSat : satisfiable φ := by
        refine ⟨Fin.init (circuitZero (n + 1)), ?_⟩
        simpa [liftedSatFormula_eq] using hBool
      exact False.elim (hUnsat hSat)
    unfold circuit_s2_sharpp_complete_reductionValue circuit_s2_sharpp_complete_parameter
    rw [hcount, hzero]
    have hpowPos : 0 < 2 ^ (n + 1) := by positivity
    rw [Nat.add_comm]
    simpa using Nat.succ_pred_eq_of_pos hpowPos

private lemma universal_compilable_collision_kernel_implies_p_np_decide_unsat_spec
    (compileDim : ℕ → ℕ)
    (compileMatrix :
      ∀ F : universal_compilable_collision_kernel_implies_p_np_formula,
        Matrix (Fin (compileDim F.1)) (Fin (compileDim F.1)) ℕ)
    (compileLeft compileRight :
      ∀ F : universal_compilable_collision_kernel_implies_p_np_formula,
        Fin (compileDim F.1) → ℕ)
    (steps : ℕ → ℕ)
    (hCompile :
      universal_compilable_collision_kernel_implies_p_np_compilation_hypothesis
        compileDim compileMatrix compileLeft compileRight steps) :
    ∀ F,
      universal_compilable_collision_kernel_implies_p_np_decide_unsat
          compileDim compileMatrix compileLeft compileRight steps F = true ↔
        universal_compilable_collision_kernel_implies_p_np_unsat F := by
  intro F
  simp [universal_compilable_collision_kernel_implies_p_np_decide_unsat,
    universal_compilable_collision_kernel_implies_p_np_unsat, hCompile F,
    universal_compilable_collision_kernel_implies_p_np_reductionValue_eq_ambient_iff_not_satisfiable]

/-- Paper label: `prop:universal-compilable-collision-kernel-implies-p-np`. A universal
polynomial-size compilation of the circuit `S₂` collision value into matrix powers yields a
polynomial-time `UNSAT` classifier by comparing the compiled value with the ambient identity term;
complementing that classifier gives the chapter-local `P = NP` consequence. -/
theorem paper_universal_compilable_collision_kernel_implies_p_np
    (compileDim : ℕ → ℕ)
    (compileMatrix :
      ∀ F : universal_compilable_collision_kernel_implies_p_np_formula,
        Matrix (Fin (compileDim F.1)) (Fin (compileDim F.1)) ℕ)
    (compileLeft compileRight :
      ∀ F : universal_compilable_collision_kernel_implies_p_np_formula,
        Fin (compileDim F.1) → ℕ)
    (steps : ℕ → ℕ)
    (hCompile :
      universal_compilable_collision_kernel_implies_p_np_compilation_hypothesis
        compileDim compileMatrix compileLeft compileRight steps) :
    Omega.SPG.UNSATInP universal_compilable_collision_kernel_implies_p_np_unsat ∧
      Omega.SPG.PEqualsNP universal_compilable_collision_kernel_implies_p_np_unsat := by
  have hSpec :
      ∀ F,
        universal_compilable_collision_kernel_implies_p_np_decide_unsat
            compileDim compileMatrix compileLeft compileRight steps F = true ↔
          universal_compilable_collision_kernel_implies_p_np_unsat F :=
    universal_compilable_collision_kernel_implies_p_np_decide_unsat_spec
      compileDim compileMatrix compileLeft compileRight steps hCompile
  have hUnsat :
      Omega.SPG.UNSATInP universal_compilable_collision_kernel_implies_p_np_unsat := by
    refine ⟨
      universal_compilable_collision_kernel_implies_p_np_decide_unsat
        compileDim compileMatrix compileLeft compileRight steps,
      trivial,
      hSpec⟩
  have hSat :
      Omega.SPG.SATInP
        (fun F => ¬ universal_compilable_collision_kernel_implies_p_np_unsat F) :=
    Omega.SPG.complement_polytime_decidable hUnsat
  exact ⟨hUnsat, ⟨hSat, hUnsat⟩⟩

end Omega.OperatorAlgebra
