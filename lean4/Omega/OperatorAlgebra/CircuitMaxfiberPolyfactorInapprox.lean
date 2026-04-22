import Mathlib.Tactic
import Omega.OperatorAlgebra.CircuitIndexGeKNPComplete
import Omega.OperatorAlgebra.FoldJonesBasicConstructionDirectsum

namespace Omega.OperatorAlgebra

open FoldJonesBasicConstructionDirectsum

/-- The exact maximum fiber size of a finite Boolean circuit. -/
def circuit_maxfiber_polyfactor_inapprox_maxfiber {n : ℕ} (C : BoolCircuit n) : ℕ :=
  Finset.univ.sup fun y => Fintype.card (foldFiber C y)

/-- A concrete multiplicative approximation guarantee for the maximum fiber size. -/
def circuit_maxfiber_polyfactor_inapprox_approximates (f : ℕ → ℕ) {n : ℕ}
    (C : BoolCircuit n) (dhat : ℕ) : Prop :=
  circuit_maxfiber_polyfactor_inapprox_maxfiber C ≤ dhat ∧
    dhat ≤ f n * circuit_maxfiber_polyfactor_inapprox_maxfiber C

/-- Concrete SAT-hardness package for thresholding a multiplicative approximation to maxfiber on
the `2n + 1`-bit padding reduction. -/
def circuit_maxfiber_polyfactor_inapprox_package (f : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, f (2 * n + 1) < 2 ^ (n + 1) →
    ∀ φ : BitVec n → Bool,
      let C := satReductionCircuitGeK (n + 1) φ
      (¬ satisfiable φ → circuit_maxfiber_polyfactor_inapprox_maxfiber C = 1) ∧
        (satisfiable φ → 2 ^ (n + 1) ≤ circuit_maxfiber_polyfactor_inapprox_maxfiber C) ∧
        ∀ dhat : ℕ, circuit_maxfiber_polyfactor_inapprox_approximates f C dhat →
          (dhat < 2 ^ (n + 1) ↔ ¬ satisfiable φ)

lemma circuit_maxfiber_polyfactor_inapprox_append_injective {n t : ℕ} (u : BitVec n) :
    Function.Injective (fun z : BitVec t => Fin.append u z) := by
  intro z z' hzz'
  funext j
  have hEval := congrArg (fun v => v (Fin.natAdd n j)) hzz'
  simpa using hEval

lemma circuit_maxfiber_polyfactor_inapprox_lifted_append {n t : ℕ}
    (φ : BitVec n → Bool) (u : BitVec n) (z : BitVec t) :
    liftedSatFormulaGeK t φ (Fin.append u z) = φ u := by
  unfold liftedSatFormulaGeK
  congr 1
  funext j
  simp

lemma circuit_maxfiber_polyfactor_inapprox_unsat_eq_self {n : ℕ} (φ : BitVec n → Bool)
    (hunsat : ¬ satisfiable φ) (a : BitVec (n + circuitIndexPaddingBits (n + 1))) :
    satReductionCircuitGeK (n + 1) φ a = a := by
  by_cases hsat : liftedSatFormulaGeK (n + 1) φ a = true
  · have : satisfiable φ := by
      refine ⟨fun j => a (Fin.castAdd (circuitIndexPaddingBits (n + 1)) j), ?_⟩
      simpa [liftedSatFormulaGeK] using hsat
    exact (hunsat this).elim
  · simp [satReductionCircuitGeK, hsat]

lemma circuit_maxfiber_polyfactor_inapprox_identity_maxfiber {m : ℕ} :
    circuit_maxfiber_polyfactor_inapprox_maxfiber (fun a : BitVec m => a) = 1 := by
  classical
  unfold circuit_maxfiber_polyfactor_inapprox_maxfiber
  refine le_antisymm ?_ ?_
  · refine Finset.sup_le ?_
    intro y hy
    simp [foldFiber]
  · have hmem : (fun _ : Fin m => false) ∈ (Finset.univ : Finset (BitVec m)) := by
      simp
    simpa [foldFiber] using Finset.le_sup hmem

/-- Paper label: `thm:circuit-maxfiber-polyfactor-inapprox`. On the `2n + 1`-bit SAT reduction,
unsatisfiable formulas give the identity circuit and therefore maxfiber `1`, while a satisfying
assignment contributes all `2^(n+1)` padding strings to the zero fiber. Any multiplicative
approximation with factor below `2^(n+1)` is therefore separated by the threshold `2^(n+1)`. -/
theorem paper_circuit_maxfiber_polyfactor_inapprox (f : ℕ → ℕ) :
    circuit_maxfiber_polyfactor_inapprox_package f := by
  intro n hf φ
  let C : BoolCircuit (n + circuitIndexPaddingBits (n + 1)) := satReductionCircuitGeK (n + 1) φ
  have hunsat_max :
      ¬ satisfiable φ → circuit_maxfiber_polyfactor_inapprox_maxfiber C = 1 := by
    intro hunsat
    dsimp [C]
    have hid : satReductionCircuitGeK (n + 1) φ = fun a => a := by
      funext a
      exact circuit_maxfiber_polyfactor_inapprox_unsat_eq_self φ hunsat a
    rw [hid]
    exact circuit_maxfiber_polyfactor_inapprox_identity_maxfiber
  have hsat_max :
      satisfiable φ → 2 ^ (n + 1) ≤ circuit_maxfiber_polyfactor_inapprox_maxfiber C := by
    intro hsat
    rcases hsat with ⟨u, hu⟩
    let zeroOut : BitVec (n + circuitIndexPaddingBits (n + 1)) :=
      circuitZero (n + circuitIndexPaddingBits (n + 1))
    let g : BitVec (n + 1) → foldFiber C zeroOut := fun z => by
      refine ⟨Fin.append u z, ?_⟩
      dsimp [C, zeroOut]
      have htrue : liftedSatFormulaGeK (n + 1) φ (Fin.append u z) = true := by
        simp [circuit_maxfiber_polyfactor_inapprox_lifted_append, hu]
      simp [satReductionCircuitGeK, htrue]
    have hg_inj : Function.Injective g := by
      intro z z' hzz'
      exact circuit_maxfiber_polyfactor_inapprox_append_injective u (congrArg Subtype.val hzz')
    have hcard :
        2 ^ (n + 1) ≤ Fintype.card (foldFiber C zeroOut) := by
      simpa [BitVec] using Fintype.card_le_of_injective g hg_inj
    have hsup :
        Fintype.card (foldFiber C zeroOut) ≤ circuit_maxfiber_polyfactor_inapprox_maxfiber C := by
      unfold circuit_maxfiber_polyfactor_inapprox_maxfiber
      have hmem : zeroOut ∈ (Finset.univ : Finset (BitVec (n + circuitIndexPaddingBits (n + 1)))) := by
        simp [zeroOut]
      exact Finset.le_sup (s := Finset.univ)
        (f := fun y : BitVec (n + circuitIndexPaddingBits (n + 1)) => Fintype.card (foldFiber C y))
        hmem
    exact le_trans hcard hsup
  refine ⟨hunsat_max, hsat_max, ?_⟩
  intro dhat hdhat
  constructor
  · intro hlt hsat
    exact not_lt_of_ge (le_trans (hsat_max hsat) hdhat.1) hlt
  · intro hunsat
    have hmax_eq :
        circuit_maxfiber_polyfactor_inapprox_maxfiber C = 1 := hunsat_max hunsat
    have hdhat2 := hdhat.2
    have hdhat_le_mul :
        dhat ≤ f (n + circuitIndexPaddingBits (n + 1)) * 1 := by
      change dhat ≤
        f (n + circuitIndexPaddingBits (n + 1)) *
          circuit_maxfiber_polyfactor_inapprox_maxfiber C at hdhat2
      rw [hmax_eq] at hdhat2
      exact hdhat2
    have hdhat_le :
        dhat ≤ f (n + circuitIndexPaddingBits (n + 1)) := by
      simpa using hdhat_le_mul
    have hf' : f (n + circuitIndexPaddingBits (n + 1)) < 2 ^ (n + 1) := by
      simpa [circuitIndexPaddingBits, two_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        using hf
    exact lt_of_le_of_lt hdhat_le hf'

end Omega.OperatorAlgebra
