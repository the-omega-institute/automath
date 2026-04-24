import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic

namespace Omega.OperatorAlgebra

/-- Boolean strings of length `n`. -/
abbrev BitVec (n : ℕ) := Fin n → Bool

/-- Boolean circuits on `n` bits, modeled extensionally as functions. -/
abbrev BoolCircuit (n : ℕ) := BitVec n → BitVec n

/-- The zero output used by the SAT reduction. -/
def circuitZero (n : ℕ) : BitVec n :=
  fun _ => false

/-- The decision problem `D(C) ≥ 2`: some output has at least two preimages. -/
def circuitMaxFiberAtLeastTwo {n : ℕ} (C : BoolCircuit n) : Prop :=
  ∃ a b : BitVec n, a ≠ b ∧ C a = C b

/-- Satisfiability of a Boolean formula. -/
def satisfiable {n : ℕ} (φ : BitVec n → Bool) : Prop :=
  ∃ a, φ a = true

/-- Append one final bit to a Boolean string. -/
def appendBit {n : ℕ} (u : BitVec n) (z : Bool) : BitVec (n + 1) :=
  @Fin.snoc _ (fun _ => Bool) u z

/-- The lifted formula `φ'(u, z) = φ(u) ∧ (z ∨ ¬z)`. -/
def liftedSatFormula {n : ℕ} (φ : BitVec n → Bool) : BitVec (n + 1) → Bool :=
  fun a => φ (Fin.init a) && (a (Fin.last n) || !a (Fin.last n))

/-- The many-one reduction sending satisfying assignments to the common zero output and all other
inputs to themselves. -/
def satReductionCircuit {n : ℕ} (φ : BitVec n → Bool) : BoolCircuit (n + 1) :=
  fun a => if liftedSatFormula φ a then circuitZero (n + 1) else a

/-- Concrete package for witness-based membership in NP together with the SAT reduction. -/
def CircuitNoninjectiveNPComplete : Prop :=
  (∀ {n : ℕ} (C : BoolCircuit n), circuitMaxFiberAtLeastTwo C →
      ∃ a b : BitVec n, a ≠ b ∧ C a = C b) ∧
    (∀ {n : ℕ} (φ : BitVec n → Bool),
      satisfiable φ ↔ circuitMaxFiberAtLeastTwo (satReductionCircuit φ))

lemma liftedSatFormula_eq {n : ℕ} (φ : BitVec n → Bool) (a : BitVec (n + 1)) :
    liftedSatFormula φ a = φ (Fin.init a) := by
  by_cases h : a (Fin.last n)
  · simp [liftedSatFormula, h]
  · simp [liftedSatFormula, h]

lemma appendBit_false_ne_true {n : ℕ} (u : BitVec n) : appendBit u false ≠ appendBit u true := by
  intro h
  have hlast := congrArg (fun v => v (Fin.last n)) h
  simp [appendBit] at hlast

theorem satReductionCircuit_spec {n : ℕ} (φ : BitVec n → Bool) :
    satisfiable φ ↔ circuitMaxFiberAtLeastTwo (satReductionCircuit φ) := by
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨appendBit u false, appendBit u true, appendBit_false_ne_true u, ?_⟩
    simp [appendBit, satReductionCircuit, liftedSatFormula_eq, hu]
  · rintro ⟨a, b, hab, habEq⟩
    by_cases ha : liftedSatFormula φ a = true
    · refine ⟨Fin.init a, ?_⟩
      simpa [liftedSatFormula_eq] using ha
    · by_cases hb : liftedSatFormula φ b = true
      · refine ⟨Fin.init b, ?_⟩
        simpa [liftedSatFormula_eq] using hb
      · have : a = b := by
          simpa [satReductionCircuit, ha, hb] using habEq
        exact (hab this).elim

/-- Paper label: `thm:circuit-noninjective-np-complete`. The decision problem is packaged by the
collision witness `(a, b)`, and the standard SAT reduction collapses all satisfying assignments to
the zero output. -/
theorem paper_circuit_noninjective_np_complete : CircuitNoninjectiveNPComplete := by
  refine ⟨?_, ?_⟩
  · intro n C hC
    exact hC
  · intro n φ
    exact satReductionCircuit_spec φ

end Omega.OperatorAlgebra
