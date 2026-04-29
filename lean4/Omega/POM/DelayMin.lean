import Mathlib.Tactic

namespace Omega.POM

/-- The ternary alphabet `{0,1,2}` used for the explicit online-kernel witness. -/
inductive TernaryDigit where
  | d0
  | d1
  | d2
deriving DecidableEq, Repr

/-- The explicit online-kernel state singled out in the paper proof. -/
def pomWitnessState : TernaryDigit × TernaryDigit × TernaryDigit :=
  (.d0, .d0, .d2)

/-- The emitted bit of the explicit online kernel at the witness state. The branch at `002`
depends on the third future symbol, which is exactly what obstructs delay `2`. -/
def pomExplicitOnlineBit :
    (TernaryDigit × TernaryDigit × TernaryDigit) → TernaryDigit → TernaryDigit → Bool
  | (.d0, .d0, .d2), .d0, .d0 => false
  | (.d0, .d0, .d2), .d0, .d1 => true
  | (.d0, .d0, .d2), .d1, .d0 => true
  | (.d0, .d0, .d2), .d1, .d1 => false
  | _, _, _ => false

/-- A delay-`2` transducer may inspect the current state and the next input symbol only. -/
abbrev DelayTwoTransducer :=
  (TernaryDigit × TernaryDigit × TernaryDigit) → TernaryDigit → Bool

/-- At the witness state `002`, the explicit kernel emits different bits on the two continuations
with the same next input `0`, so no delay-`2` transducer can reproduce the kernel. The concrete
values for next inputs `0` and `1` are also recorded explicitly.
    prop:pom-delay-min -/
def POMDelayMinStatement : Prop :=
  let s := pomWitnessState
  pomExplicitOnlineBit s .d0 .d0 = false ∧
    pomExplicitOnlineBit s .d1 .d0 = true ∧
    pomExplicitOnlineBit s .d0 .d1 = true ∧
    ¬ ∃ T : DelayTwoTransducer, ∀ d e, T s d = pomExplicitOnlineBit s d e

theorem paper_pom_delay_min : POMDelayMinStatement := by
  dsimp [POMDelayMinStatement, pomWitnessState]
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro h
  rcases h with ⟨T, hT⟩
  have h00 : T (.d0, .d0, .d2) .d0 = false := by simpa using hT .d0 .d0
  have h01 : T (.d0, .d0, .d2) .d0 = true := by simpa using hT .d0 .d1
  have : (false : Bool) = true := by simpa [h00] using h01
  cases this

end Omega.POM
