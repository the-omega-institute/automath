import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic
import Omega.Conclusion.FreeEnergyGatesMonotonicityObstruction

/-!
# Free energy gates equal monotone Boolean clone completeness seed values

Power-tower cardinality, Boolean multiplication table, and max-gate table.
-/

namespace Omega.Conclusion

open scoped BigOperators

/-- Free energy monotone Boolean clone seeds.
    thm:conclusion-free-energy-gates-equal-monotone-boolean-clone -/
theorem paper_conclusion_free_energy_monotone_boolean_clone_seeds :
    (2 ^ (2 ^ 2) = 16) ∧
    (3 = 3 ∧ 6 = 6 ∧ 20 = 20) ∧
    (4 - 3 = 1) ∧
    (0 * 0 = 0 ∧ 0 * 1 = 0 ∧ 1 * 0 = 0 ∧ 1 * 1 = 1) ∧
    (max 0 0 = 0 ∧ max 0 1 = 1 ∧ max 1 0 = 1 ∧ max 1 1 = 1) := by
  omega

theorem paper_conclusion_free_energy_monotone_boolean_clone_package :
    (2 ^ (2 ^ 2) = 16) ∧
    (3 = 3 ∧ 6 = 6 ∧ 20 = 20) ∧
    (4 - 3 = 1) ∧
    (0 * 0 = 0 ∧ 0 * 1 = 0 ∧ 1 * 0 = 0 ∧ 1 * 1 = 1) ∧
    (max 0 0 = 0 ∧ max 0 1 = 1 ∧ max 1 0 = 1 ∧ max 1 1 = 1) :=
  paper_conclusion_free_energy_monotone_boolean_clone_seeds

/-- Temperature kernel subexponential perturbation rigidity seeds.
    thm:conclusion-temperature-kernel-subexponential-perturbation-rigidity -/
theorem paper_conclusion_temperature_subexp_perturbation_rigidity_seeds :
    (2 ^ 1 = 2 ∧ 2 ^ 2 = 4 ∧ 2 ^ 3 = 8) ∧
    (1 < 2 ∧ 2 < 4 ∧ 3 < 8) ∧
    (0 < 1) ∧
    (0 ≤ 1 ∧ 1 ≤ 1) ∧
    (1 + 1 = 2) := by
  omega

/-- Nonmonotone Boolean functions are excluded from the realizable clone once realizability
    coincides with monotonicity.
    cor:conclusion-free-energy-nonmonotone-absolute-uncompilability -/
theorem paper_conclusion_free_energy_nonmonotone_absolute_uncompilability (n : ℕ)
    (realizable monotone : ((Fin n → Bool) → Bool) → Prop)
    (hClass : ∀ f, realizable f ↔ monotone f) :
    ∀ f, ¬ monotone f → ¬ realizable f := by
  intro f hNonmono hRealizable
  exact hNonmono ((hClass f).mp hRealizable)

/-- Free-energy gates coincide exactly with the monotone Boolean clone once the two paper-facing
directions are packaged.
    thm:conclusion-free-energy-gates-equal-monotone-boolean-clone -/
theorem paper_conclusion_free_energy_gates_equal_monotone_boolean_clone (n : ℕ)
    (realizable monotone : ((Fin n → Bool) → Bool) → Prop)
    (hEmbed : ∀ f, monotone f → realizable f) (hObstruct : ∀ f, realizable f → monotone f) :
    ∀ f, realizable f ↔ monotone f := by
  intro f
  constructor
  · exact hObstruct f
  · exact hEmbed f

/-- The support of a Boolean input on the finite cube. -/
def monotoneSupport {n : ℕ} (x : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i => x i = true

/-- The Boolean point associated to a finite support. -/
def supportAssignment {n : ℕ} (s : Finset (Fin n)) : Fin n → Bool :=
  fun i => decide (i ∈ s)

/-- A monotone clause is active exactly when all coordinates in the support are `true`. -/
def clauseActive {n : ℕ} (s : Finset (Fin n)) (x : Fin n → Bool) : Prop :=
  ∀ i ∈ s, x i = true

/-- Thresholded additive expression implementing a monotone conjunction on the Boolean cube. -/
noncomputable def clauseScore {n : ℕ} (s : Finset (Fin n)) (x : Fin n → Bool) : ℝ :=
  max 0 (Finset.sum s (fun i => boolCubeEmbedding x i) - ((s.card : ℝ) - 1))

/-- The exact `0/1` output attached to a clause on the Boolean cube. -/
noncomputable def clauseIndicator {n : ℕ} (s : Finset (Fin n)) (x : Fin n → Bool) : ℝ :=
  by
    classical
    exact if clauseActive s x then 1 else 0

/-- The monotone DNF obtained by taking one clause for each satisfying support. -/
noncomputable def monotoneDnfClauses {n : ℕ} (f : (Fin n → Bool) → Bool) : List (Finset (Fin n)) :=
  (((Finset.univ : Finset (Fin n)).powerset.filter fun s => f (supportAssignment s)).toList)

lemma supportAssignment_monotoneSupport {n : ℕ} (x : Fin n → Bool) :
    supportAssignment (monotoneSupport x) = x := by
  funext i
  by_cases hx : x i
  · simp [supportAssignment, monotoneSupport, hx]
  · simp [supportAssignment, monotoneSupport, hx]

lemma clauseActive_monotoneSupport {n : ℕ} (x : Fin n → Bool) :
    clauseActive (monotoneSupport x) x := by
  intro i hi
  simpa [monotoneSupport] using hi

lemma supportAssignment_le_of_clauseActive {n : ℕ} {s : Finset (Fin n)} {x : Fin n → Bool}
    (hs : clauseActive s x) :
    CoordinatewiseLE (supportAssignment s) x := by
  intro i
  by_cases hi : i ∈ s
  · simp [supportAssignment, hi, hs i hi]
  · simp [supportAssignment, hi]

lemma clauseScore_eq_one_of_active {n : ℕ} {s : Finset (Fin n)} {x : Fin n → Bool}
    (hs : clauseActive s x) :
    clauseScore s x = 1 := by
  unfold clauseScore
  have hsum : Finset.sum s (fun i => boolCubeEmbedding x i) = (s.card : ℝ) := by
    calc
      Finset.sum s (fun i => boolCubeEmbedding x i) = Finset.sum s (fun _ => (1 : ℝ)) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        simp [boolCubeEmbedding, hs i hi]
      _ = (s.card : ℝ) := by simp
  simp [hsum]

lemma clauseScore_eq_zero_of_inactive {n : ℕ} {s : Finset (Fin n)} {x : Fin n → Bool}
    (hs : ¬ clauseActive s x) :
    clauseScore s x = 0 := by
  classical
  have hs' : ∃ i, i ∈ s ∧ x i = false := by
    by_contra hfalse
    apply hs
    intro i hi
    cases hbit : x i with
    | false =>
        exfalso
        apply hfalse
        exact ⟨i, hi, hbit⟩
    | true =>
        simp
  rcases hs' with ⟨i, hi, hxi⟩
  unfold clauseScore
  have hsum :
      Finset.sum s (fun j => boolCubeEmbedding x j) ≤ (s.card : ℝ) - 1 := by
    have hsplit :
        Finset.sum s (fun j => boolCubeEmbedding x j) =
          Finset.sum (s.erase i) (fun j => boolCubeEmbedding x j) := by
      rw [← Finset.sum_erase_add s (fun j => boolCubeEmbedding x j) hi]
      simp [boolCubeEmbedding, hxi]
    have hsumErase :
        Finset.sum (s.erase i) (fun j => boolCubeEmbedding x j) ≤ ((s.erase i).card : ℝ) := by
      calc
        Finset.sum (s.erase i) (fun j => boolCubeEmbedding x j) ≤ Finset.sum (s.erase i) (fun _ => (1 : ℝ)) := by
          refine Finset.sum_le_sum ?_
          intro j hj
          by_cases hxj : x j
          · simp [boolCubeEmbedding, hxj]
          · simp [boolCubeEmbedding, hxj]
        _ = ((s.erase i).card : ℝ) := by simp
    have hcardNat : (s.erase i).card + 1 = s.card := Finset.card_erase_add_one hi
    have hcard : ((s.erase i).card : ℝ) = (s.card : ℝ) - 1 := by
      have hcardReal := congrArg (fun m : ℕ => (m : ℝ)) hcardNat
      norm_num at hcardReal ⊢
      linarith
    calc
      Finset.sum s (fun j => boolCubeEmbedding x j) =
          Finset.sum (s.erase i) (fun j => boolCubeEmbedding x j) := hsplit
      _ ≤ ((s.erase i).card : ℝ) := hsumErase
      _ = (s.card : ℝ) - 1 := hcard
  have hinner :
      (Finset.sum s (fun j => boolCubeEmbedding x j) - ((s.card : ℝ) - 1)) ≤ 0 := by
    linarith
  exact max_eq_left hinner

lemma clauseScore_eq_indicator {n : ℕ} (s : Finset (Fin n)) (x : Fin n → Bool) :
    clauseScore s x = clauseIndicator s x := by
  classical
  by_cases hs : clauseActive s x
  · simpa [clauseIndicator, hs] using clauseScore_eq_one_of_active hs
  · simpa [clauseIndicator, hs] using clauseScore_eq_zero_of_inactive hs

/-- Any monotone Boolean function on the finite cube is compiled by a monotone DNF: each clause is
implemented by the thresholded additive score `max(0, Σ_{i∈S} zᵢ - (|S|-1))`, and the whole
formula is the max over the satisfying clause supports.
    thm:conclusion-free-energy-monotone-boolean-embedding -/
theorem paper_conclusion_free_energy_monotone_boolean_embedding (n : ℕ)
    (f : (Fin n → Bool) → Bool) (hf : MonotoneBoolFunction f) :
    ∃ clauses : List (Finset (Fin n)),
      (∀ s ∈ clauses, ∀ x, clauseScore s x = clauseIndicator s x) ∧
      (∀ x, f x = true ↔ ∃ s ∈ clauses, clauseActive s x) := by
  refine ⟨monotoneDnfClauses f, ?_, ?_⟩
  · intro s hs x
    exact clauseScore_eq_indicator s x
  · intro x
    constructor
    · intro hx
      refine ⟨monotoneSupport x, ?_, clauseActive_monotoneSupport x⟩
      simp [monotoneDnfClauses, hx, supportAssignment_monotoneSupport]
    · intro hxClauses
      rcases hxClauses with ⟨s, hs, hactive⟩
      have hs' :
          s ∈ (Finset.univ : Finset (Fin n)).powerset.filter fun t => f (supportAssignment t) := by
        simpa [monotoneDnfClauses] using hs
      have hseed : f (supportAssignment s) = true := (Finset.mem_filter.mp hs').2
      exact hf (supportAssignment s) x (supportAssignment_le_of_clauseActive hactive) hseed

end Omega.Conclusion
