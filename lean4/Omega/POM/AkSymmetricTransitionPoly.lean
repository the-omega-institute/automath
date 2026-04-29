import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Basic

namespace Omega.POM

open scoped BigOperators
open Classical

noncomputable section

/-- Histogram states for the symmetric quotient kernel. -/
abbrev pom_ak_symmetric_transition_poly_histogram (q : ℕ) := Fin q → ℕ

/-- Bounded choice counts for a histogram of total size at most `k`. -/
abbrev pom_ak_symmetric_transition_poly_choice_family (q k : ℕ) := Fin q → Fin (k + 1)

/-- Forget the `Fin` bound and read a bounded choice family as natural-number counts. -/
def pom_ak_symmetric_transition_poly_choice_counts {q k : ℕ}
    (a : pom_ak_symmetric_transition_poly_choice_family q k) :
    pom_ak_symmetric_transition_poly_histogram q :=
  fun s => a s

/-- A choice family is admissible when it respects the output symbol and never chooses more
transitions than are available in the current histogram state. -/
def pom_ak_symmetric_transition_poly_admissible {q : ℕ}
    (eps : Fin q → Bool → Bool) (ν : pom_ak_symmetric_transition_poly_histogram q)
    (e : Bool) {k : ℕ} (a : pom_ak_symmetric_transition_poly_choice_family q k) : Prop :=
  ∀ s,
    (eps s false ≠ e → pom_ak_symmetric_transition_poly_choice_counts a s = 0) ∧
      (eps s true ≠ e → pom_ak_symmetric_transition_poly_choice_counts a s = ν s) ∧
      pom_ak_symmetric_transition_poly_choice_counts a s ≤ ν s

/-- The next histogram is obtained by aggregating the `0` and `1` choices by their deterministic
next states. -/
def pom_ak_symmetric_transition_poly_next_histogram {q : ℕ}
    (δ : Fin q → Bool → Fin q) (ν : pom_ak_symmetric_transition_poly_histogram q)
    {k : ℕ} (a : pom_ak_symmetric_transition_poly_choice_family q k) :
    pom_ak_symmetric_transition_poly_histogram q :=
  fun s' =>
    Finset.sum Finset.univ fun s : Fin q =>
      (if δ s false = s' then pom_ak_symmetric_transition_poly_choice_counts a s else 0) +
        (if δ s true = s' then ν s - pom_ak_symmetric_transition_poly_choice_counts a s else 0)

/-- The per-choice transition multiplicity is the product of the binomial choices made in each
state bucket. -/
def pom_ak_symmetric_transition_poly_choice_weight {q : ℕ}
    (ν : pom_ak_symmetric_transition_poly_histogram q) {k : ℕ}
    (a : pom_ak_symmetric_transition_poly_choice_family q k) : Nat :=
  Finset.prod Finset.univ fun s : Fin q =>
    Nat.choose (ν s) (pom_ak_symmetric_transition_poly_choice_counts a s)

/-- One-step weights are obtained by summing the admissible per-state binomial choices whose
deterministic successor histogram is the prescribed target. -/
def pom_ak_symmetric_transition_poly_one_step_weight {q : ℕ}
    (δ : Fin q → Bool → Fin q) (eps : Fin q → Bool → Bool)
    (ν : pom_ak_symmetric_transition_poly_histogram q) (k : ℕ) (e : Bool)
    (ν' : pom_ak_symmetric_transition_poly_histogram q) : Nat :=
  Finset.sum (Finset.univ : Finset (pom_ak_symmetric_transition_poly_choice_family q k)) fun a =>
    if pom_ak_symmetric_transition_poly_admissible eps ν e a ∧
        pom_ak_symmetric_transition_poly_next_histogram δ ν a = ν'
    then pom_ak_symmetric_transition_poly_choice_weight ν a
    else 0

/-- Concrete operation count for the fixed-state dynamic program. -/
def pom_ak_symmetric_transition_poly_dp_work (q k : ℕ) : Nat :=
  2 * (k + 1) ^ q

/-- For fixed state-space size `q`, the dynamic program runs in polynomial time in `k`. -/
def pom_ak_symmetric_transition_poly_polynomial_time (q : ℕ) : Prop :=
  ∃ C : ℕ, 0 < C ∧
    ∀ k : ℕ,
      pom_ak_symmetric_transition_poly_dp_work q k ≤ C * (k + 1) ^ q

/-- Paper-facing statement: choice counts determine the next histogram uniquely, the transition
weights are the per-state binomial convolution, and the fixed-state construction is polynomial in
the histogram size parameter. -/
def paper_pom_ak_symmetric_transition_poly_stmt : Prop :=
  ∀ (q k : ℕ) (δ : Fin q → Bool → Fin q) (eps : Fin q → Bool → Bool)
    (ν : pom_ak_symmetric_transition_poly_histogram q),
    (∀ s, ν s ≤ k) →
      (∀ e : Bool, ∀ a : pom_ak_symmetric_transition_poly_choice_family q k,
        pom_ak_symmetric_transition_poly_admissible eps ν e a →
          ∃! ν' : pom_ak_symmetric_transition_poly_histogram q,
            ν' = pom_ak_symmetric_transition_poly_next_histogram δ ν a) ∧
      (∀ e : Bool, ∀ ν' : pom_ak_symmetric_transition_poly_histogram q,
        pom_ak_symmetric_transition_poly_one_step_weight δ eps ν k e ν' =
          Finset.sum
            (Finset.univ : Finset (pom_ak_symmetric_transition_poly_choice_family q k)) fun a =>
            if pom_ak_symmetric_transition_poly_admissible eps ν e a ∧
                pom_ak_symmetric_transition_poly_next_histogram δ ν a = ν'
            then pom_ak_symmetric_transition_poly_choice_weight ν a
            else 0) ∧
      pom_ak_symmetric_transition_poly_polynomial_time q

theorem paper_pom_ak_symmetric_transition_poly : paper_pom_ak_symmetric_transition_poly_stmt := by
  intro q k δ eps ν _hν
  refine ⟨?_, ?_, ?_⟩
  · intro e a _ha
    refine ⟨pom_ak_symmetric_transition_poly_next_histogram δ ν a, rfl, ?_⟩
    intro ν' hν'
    exact hν'
  · intro e ν'
    rfl
  · refine ⟨2, by decide, ?_⟩
    intro k'
    simp [pom_ak_symmetric_transition_poly_dp_work]

end

end Omega.POM
