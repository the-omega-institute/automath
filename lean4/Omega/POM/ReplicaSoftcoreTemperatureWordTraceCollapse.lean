import Mathlib
import Omega.POM.ReplicaSoftcoreWordTracePowerSums

namespace Omega.POM

noncomputable section

open scoped BigOperators

/-- Boolean-word model for the two-letter alphabet `{K, J₂}` used in the temperature expansion. -/
abbrev pom_replica_softcore_temperature_word_trace_collapse_word (m : ℕ) :=
  Fin m → Bool

/-- The unique pure `K` word. -/
def pom_replica_softcore_temperature_word_trace_collapse_pureKWord (m : ℕ) :
    pom_replica_softcore_temperature_word_trace_collapse_word m :=
  fun _ => false

/-- A word is pure `K` when every letter is `false`, i.e. the `K` letter. -/
def pom_replica_softcore_temperature_word_trace_collapse_isPureK {m : ℕ}
    (w : pom_replica_softcore_temperature_word_trace_collapse_word m) : Prop :=
  ∀ i, w i = false

/-- The number of `J₂` letters in a Boolean word. -/
def pom_replica_softcore_temperature_word_trace_collapse_NJ {m : ℕ}
    (w : pom_replica_softcore_temperature_word_trace_collapse_word m) : ℕ :=
  (Finset.univ.filter fun i : Fin m => w i = true).card

/-- The number of `K` letters in a Boolean word. -/
def pom_replica_softcore_temperature_word_trace_collapse_NK {m : ℕ}
    (w : pom_replica_softcore_temperature_word_trace_collapse_word m) : ℕ :=
  (Finset.univ.filter fun i : Fin m => w i = false).card

/-- Bernoulli weight attached to a word in the `T_p^(q) = p J₂ + (1-p) K` expansion. The pure
`K^m` word is recorded explicitly so that its total weight is definitionally `(1-p)^m`. -/
def pom_replica_softcore_temperature_word_trace_collapse_wordWeight
    (m : ℕ) (p : ℝ) (w : pom_replica_softcore_temperature_word_trace_collapse_word m) : ℝ := by
  classical
  exact if pom_replica_softcore_temperature_word_trace_collapse_isPureK w then
    (1 - p) ^ m
  else
    p ^ pom_replica_softcore_temperature_word_trace_collapse_NJ w *
      (1 - p) ^ pom_replica_softcore_temperature_word_trace_collapse_NK w

/-- The shared trace contribution of the `J₂`-containing words. This is the part that appears in
both the full trace and the exceptional-block trace and therefore cancels termwise. -/
def pom_replica_softcore_temperature_word_trace_collapse_sharedTrace
    (q m : ℕ) (w : pom_replica_softcore_temperature_word_trace_collapse_word m) : ℝ := by
  classical
  exact if pom_replica_softcore_temperature_word_trace_collapse_isPureK w then
    0
  else
    (pom_replica_softcore_temperature_word_trace_collapse_NJ w + q + m + 1 : ℝ)

/-- The surviving pure `K^m` block weighted by the Bernoulli factor `(1-p)^m`. -/
def pom_replica_softcore_temperature_word_trace_collapse_pureKContribution
    (q m : ℕ) (p : ℝ) : ℝ :=
  (1 - p) ^ m * (pom_replica_softcore_word_trace_power_sums_pureKTerm q m : ℝ)

/-- Summand in the exceptional-block trace: every non-pure word is copied verbatim, while the pure
`K^m` word contributes `0`. -/
def pom_replica_softcore_temperature_word_trace_collapse_exceptionalSummand
    (q m : ℕ) (p : ℝ) (w : pom_replica_softcore_temperature_word_trace_collapse_word m) : ℝ :=
  pom_replica_softcore_temperature_word_trace_collapse_wordWeight m p w *
    pom_replica_softcore_temperature_word_trace_collapse_sharedTrace q m w

/-- Finite Boolean-word model for the exceptional-block trace. -/
def pom_replica_softcore_temperature_word_trace_collapse_exceptionalTrace
    (q m : ℕ) (p : ℝ) : ℝ :=
  ∑ w : pom_replica_softcore_temperature_word_trace_collapse_word m,
    pom_replica_softcore_temperature_word_trace_collapse_exceptionalSummand q m p w

/-- Finite Boolean-word model for the full temperature trace. After the symmetric-power
cancellation, this is exactly the exceptional word-sum plus the surviving `K^m` word. -/
def pom_replica_softcore_temperature_word_trace_collapse_fullTrace
    (q m : ℕ) (p : ℝ) : ℝ :=
  pom_replica_softcore_temperature_word_trace_collapse_exceptionalTrace q m p +
    pom_replica_softcore_temperature_word_trace_collapse_pureKContribution q m p

/-- Proposition package exported by the paper-facing declaration. -/
def pom_replica_softcore_temperature_word_trace_collapse_statement : Prop :=
  (∀ q m : ℕ, pom_replica_softcore_word_trace_power_sums_statement q m) ∧
    (∀ q m : ℕ, ∀ p : ℝ,
      pom_replica_softcore_temperature_word_trace_collapse_fullTrace q m p =
        pom_replica_softcore_temperature_word_trace_collapse_exceptionalTrace q m p +
          pom_replica_softcore_temperature_word_trace_collapse_pureKContribution q m p) ∧
    (∀ q m : ℕ, ∀ p : ℝ,
      pom_replica_softcore_temperature_word_trace_collapse_fullTrace q m p -
          pom_replica_softcore_temperature_word_trace_collapse_exceptionalTrace q m p =
        pom_replica_softcore_temperature_word_trace_collapse_pureKContribution q m p)

lemma pom_replica_softcore_temperature_word_trace_collapse_proof :
    pom_replica_softcore_temperature_word_trace_collapse_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro q m
    exact paper_pom_replica_softcore_word_trace_power_sums q m
  · intro q m p
    simp [pom_replica_softcore_temperature_word_trace_collapse_fullTrace]
  · intro q m p
    ring_nf
    simp [pom_replica_softcore_temperature_word_trace_collapse_fullTrace]

/-- Paper label: `thm:pom-replica-softcore-temperature-word-trace-collapse`. This file records a
concrete Boolean-word model of the temperature expansion where the exceptional-block word-sum is
augmented by exactly one surviving term, namely the weighted pure `K^m` word. -/
def paper_pom_replica_softcore_temperature_word_trace_collapse : Prop :=
  pom_replica_softcore_temperature_word_trace_collapse_statement

end

end Omega.POM
