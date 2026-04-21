import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic
import Omega.OperatorAlgebra.CircuitNoninjectiveNPComplete

namespace Omega.OperatorAlgebra

/-- We use `k` padding bits; this is enough because `k ≤ 2^k`. -/
def circuitIndexPaddingBits (k : ℕ) : ℕ := k

/-- A `k`-collision witness is a common output together with `k` distinct preimages. -/
def circuitIndexAtLeastK {n : ℕ} (k : ℕ) (C : BoolCircuit n) : Prop :=
  ∃ y : BitVec n, ∃ w : Fin k → BitVec n, Function.Injective w ∧ ∀ i, C (w i) = y

/-- The SAT reduction ignores the padding coordinates. -/
def liftedSatFormulaGeK {n : ℕ} (k : ℕ) (φ : BitVec n → Bool) :
    BitVec (n + circuitIndexPaddingBits k) → Bool :=
  fun a => φ (fun i => a (Fin.castAdd (circuitIndexPaddingBits k) i))

/-- The reduction collapses satisfying assignments to the zero output and leaves all others fixed. -/
def satReductionCircuitGeK {n : ℕ} (k : ℕ) (φ : BitVec n → Bool) :
    BoolCircuit (n + circuitIndexPaddingBits k) :=
  fun a => if liftedSatFormulaGeK k φ a then circuitZero (n + circuitIndexPaddingBits k) else a

/-- Chapter-local NP-completeness package: enough padding bits, witness-based membership, and the
SAT reduction. -/
def CircuitIndexGeKNPComplete (k : ℕ) : Prop :=
  k ≤ 2 ^ circuitIndexPaddingBits k ∧
    (∀ {n : ℕ} (C : BoolCircuit n), circuitIndexAtLeastK k C →
      ∃ y : BitVec n, ∃ w : Fin k → BitVec n, Function.Injective w ∧ ∀ i, C (w i) = y) ∧
    (∀ {n : ℕ} (φ : BitVec n → Bool),
      satisfiable φ ↔ circuitIndexAtLeastK k (satReductionCircuitGeK k φ))

/-- A concrete family of pairwise distinct padding strings: the one-hot codes. -/
def circuitIndexPadCode {k : ℕ} (i : Fin k) : BitVec (circuitIndexPaddingBits k) :=
  fun j => decide (j = i)

/-- Attach the `i`-th padding code to the base assignment `u`. -/
def circuitIndexPaddedAssignment {n k : ℕ} (u : BitVec n) (i : Fin k) :
    BitVec (n + circuitIndexPaddingBits k) :=
  Fin.append u (circuitIndexPadCode i)

lemma self_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ihn =>
      have hstep : n + 1 ≤ 2 ^ n + 1 := Nat.succ_le_succ ihn
      have hpow : 2 ^ n + 1 ≤ 2 ^ (n + 1) := by
        calc
          2 ^ n + 1 ≤ 2 ^ n + 2 ^ n := Nat.add_le_add_left Nat.one_le_two_pow _
          _ = 2 ^ (n + 1) := by rw [Nat.pow_succ, Nat.mul_comm, two_mul]
      exact hstep.trans hpow

lemma circuitIndexPadCode_injective {k : ℕ} :
    Function.Injective (@circuitIndexPadCode k) := by
  intro i j hij
  have hEval := congrArg (fun v => v i) hij
  simpa [circuitIndexPadCode] using hEval

lemma circuitIndexPaddedAssignment_injective {n k : ℕ} (u : BitVec n) :
    Function.Injective (circuitIndexPaddedAssignment (n := n) (k := k) u) := by
  intro i j hij
  exact circuitIndexPadCode_injective <| by
    funext r
    have hEval := congrArg (fun v => v (Fin.natAdd n r)) hij
    simpa [circuitIndexPaddedAssignment] using hEval

lemma liftedSatFormulaGeK_padded {n k : ℕ} (φ : BitVec n → Bool) (u : BitVec n) (i : Fin k) :
    liftedSatFormulaGeK k φ (circuitIndexPaddedAssignment (n := n) (k := k) u i) = φ u := by
  unfold liftedSatFormulaGeK circuitIndexPaddedAssignment circuitIndexPaddingBits
  congr 1
  funext j
  simp

theorem satReductionCircuitGeK_spec {n : ℕ} (k : ℕ) (hk : 2 ≤ k) (φ : BitVec n → Bool) :
    satisfiable φ ↔ circuitIndexAtLeastK k (satReductionCircuitGeK k φ) := by
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨circuitZero (n + circuitIndexPaddingBits k), circuitIndexPaddedAssignment u,
      circuitIndexPaddedAssignment_injective u, ?_⟩
    intro i
    have hsat : liftedSatFormulaGeK k φ (circuitIndexPaddedAssignment u i) = true := by
      simpa [liftedSatFormulaGeK_padded] using hu
    simp [satReductionCircuitGeK, hsat]
  · rintro ⟨y, w, hw_inj, hw⟩
    by_cases htrue : ∃ i, liftedSatFormulaGeK k φ (w i) = true
    · rcases htrue with ⟨i, hi⟩
      refine ⟨fun j => w i (Fin.castAdd (circuitIndexPaddingBits k) j), ?_⟩
      simpa [liftedSatFormulaGeK] using hi
    · have hfalse : ∀ i, liftedSatFormulaGeK k φ (w i) = false := by
        intro i
        cases hval : liftedSatFormulaGeK k φ (w i) with
        | false =>
            rfl
        | true =>
            exact False.elim (htrue ⟨i, hval⟩)
      let i0 : Fin k := ⟨0, by omega⟩
      let i1 : Fin k := ⟨1, by omega⟩
      have hi0 : w i0 = y := by
        simpa [satReductionCircuitGeK, hfalse i0] using hw i0
      have hi1 : w i1 = y := by
        simpa [satReductionCircuitGeK, hfalse i1] using hw i1
      have hneq : i0 ≠ i1 := by
        simp [i0, i1]
      exact False.elim <| hneq <| hw_inj <| hi0.trans hi1.symm

/-- Paper label: `thm:circuit-index-ge-k-np-complete`. We use `k` padding bits, so
`2 ^ circuitIndexPaddingBits k = 2 ^ k ≥ k`; a satisfying assignment yields `k` distinct
one-hot padded preimages of the zero output, while unsatisfiability forces the reduction to act
injectively on any claimed `k`-collision witness. -/
theorem paper_circuit_index_ge_k_np_complete (k : Nat) (hk : 2 <= k) :
    CircuitIndexGeKNPComplete k := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [circuitIndexPaddingBits] using self_le_two_pow k
  · intro n C hC
    exact hC
  · intro n φ
    exact satReductionCircuitGeK_spec k hk φ

end Omega.OperatorAlgebra
