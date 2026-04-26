import Mathlib.Tactic

namespace List

/-- Local fallback for `List.get!` in environments where only `getD` is available. -/
def get! [Inhabited α] (l : List α) (n : Nat) : α :=
  l.getD n default

end List

namespace Omega.POM

/-- Signed update of a single prime exponent. Negative results are clipped to `0`. -/
def primeExpAdd (n : Nat) (z : Int) : Nat :=
  Int.toNat ((n : Int) + z)

/-- Coordinatewise addition of a prime-exponent vector with a signed delta vector. -/
def primeVecAdd : List Nat → List Int → List Nat
  | [], _ => []
  | r :: rs, [] => r :: rs
  | r :: rs, z :: zs => primeExpAdd r z :: primeVecAdd rs zs

/-- Coordinatewise threshold satisfaction for the denominator exponents of a FRACTRAN rule. -/
def primeVecThresholdSatisfied : List Nat → List Nat → Bool
  | [], _ => true
  | req :: reqs, [] => decide (req = 0) && primeVecThresholdSatisfied reqs []
  | req :: reqs, r :: rs => decide (req ≤ r) && primeVecThresholdSatisfied reqs rs

/-- In the finite prime-vector model, denominator divisibility is the threshold condition. -/
def ruleDenominatorDivides (req r : List Nat) : Prop :=
  primeVecThresholdSatisfied req r = true

/-- A FRACTRAN rule is feasible exactly when its denominator exponents divide the register state. -/
def feasibleRule (rule : List Nat × List Int) (r : List Nat) : Prop :=
  ruleDenominatorDivides rule.1 r

instance instDecidableFeasibleRule (rule : List Nat × List Int) (r : List Nat) :
    Decidable (feasibleRule rule r) := by
  unfold feasibleRule ruleDenominatorDivides
  infer_instance

theorem feasibleRule_iff_threshold_satisfied (rule : List Nat × List Int) (r : List Nat) :
    feasibleRule rule r ↔ primeVecThresholdSatisfied rule.1 r = true := by
  rfl

/-- First feasible rule in the priority list. -/
def firstFeasibleRule? : List (List Nat × List Int) → List Nat → Option Nat
  | [], _ => none
  | rule :: rules, r =>
      if feasibleRule rule r then
        some 0
      else
        Option.map Nat.succ (firstFeasibleRule? rules r)

/-- Deterministic one-step update in the prime-exponent model. -/
def stepPrimeVec (rules : List (List Nat × List Int)) (r : List Nat) : Option (List Nat) :=
  match firstFeasibleRule? rules r with
  | none => none
  | some i => some (primeVecAdd r (rules.get! i).2)

/-- Paper label: `prop:pom-fractran-prime-translation`. -/
theorem paper_pom_fractran_prime_translation (rules : List (List Nat × List Int)) (r : List Nat) :
    stepPrimeVec rules r =
      match firstFeasibleRule? rules r with
      | none => none
      | some i => some (primeVecAdd r (rules.get! i).2) := by
  rfl

end Omega.POM
