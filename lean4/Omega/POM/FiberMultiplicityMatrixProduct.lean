import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

/-- A deterministic finite-state counter for output words. The state update is deterministic, and
the terminal readout carries the final multiplicity contribution. -/
structure FiberMultiplicityAutomaton where
  State : Type
  step : State → Bool → State
  start : State
  accept : State → ℕ

namespace FiberMultiplicityAutomaton

variable (A : FiberMultiplicityAutomaton)

/-- Run the automaton from an arbitrary state along a finite output word. -/
def runFrom : A.State → List Bool → A.State
  | s, [] => s
  | s, b :: w => runFrom (A.step s b) w

/-- Run the automaton from the distinguished start state. -/
def run (w : List Bool) : A.State :=
  A.runFrom A.start w

/-- The symbol matrix attached to a single output bit. Its entries are `0` or `1` because the
update is deterministic. -/
def symbolMatrix [DecidableEq A.State] (b : Bool) : A.State → A.State → ℕ :=
  fun s t => if A.step s b = t then 1 else 0

/-- The word matrix obtained by multiplying the symbol matrices along the output word. -/
def wordMatrix [Fintype A.State] [DecidableEq A.State] : List Bool → A.State → A.State → ℕ
  | [], s, t => if s = t then 1 else 0
  | b :: w, s, t => ∑ u, A.symbolMatrix b s u * wordMatrix w u t

/-- The multiplicity read out from the final deterministic state. -/
def fiberMultiplicity (w : List Bool) : ℕ :=
  A.accept (A.run w)

lemma wordMatrix_eq_delta [Fintype A.State] [DecidableEq A.State] :
    ∀ (w : List Bool) (s t : A.State),
      A.wordMatrix w s t = if A.runFrom s w = t then 1 else 0 := by
  intro w
  induction w with
  | nil =>
      intro s t
      simp [wordMatrix, runFrom]
  | cons b w ih =>
      intro s t
      dsimp [wordMatrix, runFrom]
      let u0 := A.step s b
      calc
        ∑ u, A.symbolMatrix b s u * A.wordMatrix w u t
            = ∑ u, (if u0 = u then 1 else 0) * (if A.runFrom u w = t then 1 else 0) := by
                simp [symbolMatrix, ih, u0]
        _ = if A.runFrom u0 w = t then 1 else 0 := by
              rw [Finset.sum_eq_single u0]
              · simp
              · intro u _ hu
                have hu' : ¬u0 = u := by
                  exact fun h => hu h.symm
                simp [hu']
              · intro hu
                simp at hu
        _ = if A.runFrom s (b :: w) = t then 1 else 0 := by
              simp [FiberMultiplicityAutomaton.runFrom, u0]

/-- Matrix-product formulation of the deterministic path count. -/
def matrixProductRepresentation [Fintype A.State] [DecidableEq A.State] : Prop :=
  ∀ w : List Bool, (∑ t, A.wordMatrix w A.start t * A.accept t) = A.fiberMultiplicity w

/-- Two states are follower-ambiguous when they induce the same one-step continuation profile. -/
def followerSignature (s : A.State) : Bool → A.State :=
  fun b => A.step s b

/-- The realized follower ambiguity classes. -/
def followerAmbiguityClasses [Fintype A.State] [DecidableEq A.State] [DecidableEq (Bool → A.State)] :
    Finset (Bool → A.State) :=
  Finset.univ.image A.followerSignature

/-- The number of follower-ambiguity classes is bounded by the number of original states. -/
def minimalStateBound [Fintype A.State] [DecidableEq A.State] [DecidableEq (Bool → A.State)] :
    Prop :=
  A.followerAmbiguityClasses.card ≤ Fintype.card A.State

end FiberMultiplicityAutomaton

/-- Paper-facing package: deterministic finite-window inverse code gives a symbol-matrix product
formula for every output word, and the follower-ambiguity quotient never uses more classes than
the original state set.
    thm:pom-fiber-multiplicity-matrix-product -/
theorem paper_pom_fiber_multiplicity_matrix_product (A : FiberMultiplicityAutomaton)
    [Fintype A.State] [DecidableEq A.State] [DecidableEq (Bool → A.State)] :
    A.matrixProductRepresentation ∧ A.minimalStateBound := by
  refine ⟨?_, ?_⟩
  · intro w
    calc
      ∑ t, A.wordMatrix w A.start t * A.accept t
          = ∑ t, (if A.run w = t then 1 else 0) * A.accept t := by
              simp [FiberMultiplicityAutomaton.wordMatrix_eq_delta, FiberMultiplicityAutomaton.run]
      _ = A.accept (A.run w) := by
            rw [Finset.sum_eq_single (A.run w)]
            · simp
            · intro t _ ht
              have ht' : ¬A.run w = t := by
                exact fun h => ht h.symm
              simp [ht']
            · intro ht
              simp at ht
      _ = A.fiberMultiplicity w := rfl
  · simpa [FiberMultiplicityAutomaton.minimalStateBound,
      FiberMultiplicityAutomaton.followerAmbiguityClasses] using
      (Finset.card_image_le (s := (Finset.univ : Finset A.State))
        (f := FiberMultiplicityAutomaton.followerSignature A))

end Omega.POM
