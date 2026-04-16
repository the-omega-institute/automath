import Mathlib.Logic.Relation
import Omega.EA.PrimeRegisterNormalFormUniqueness
import Omega.EA.RewriteTermination

namespace Omega.EA

open Omega.Rewrite

/-- Paper-facing wrapper for the prime-register rewrite system: every local rewrite preserves the
    prime-register valuation, the rewrite relation is strongly terminating, and every starting
    state has the unique irreducible descendant `NF_pr`.
    prop:prime-register-rewrite-confluent-normal-form -/
theorem paper_prime_register_rewrite_confluent_normal_form :
    (∀ a b : DigitCfg, Step a b → valPr b = valPr a) ∧
      WellFounded (flip Step) ∧
      (∀ a : DigitCfg, Relation.ReflTransGen Step a (NF_pr a) ∧
        Irreducible (NF_pr a) ∧
        ∀ b : DigitCfg, Relation.ReflTransGen Step a b → Irreducible b → b = NF_pr a) := by
  refine ⟨?_, Omega.Rewrite.step_stronglyTerminating, ?_⟩
  · intro a b hStep
    simpa [valPr, Rewrite.value, Rewrite.weighted, Rewrite.digitWeight] using step_value hStep
  · intro a
    simpa using paper_prime_register_normal_form_uniqueness a

end Omega.EA
