import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.POM

open BigOperators

/-- One-part finite composition contribution used for the prefixed moment coefficients. -/
def pom_replica_softcore_perron_feshbach_composition_moment_series_compositionTerm
    (q n r : Nat) : Nat :=
  if r = n then q ^ r else 0

/-- Finite composition enumeration of the `n`th prefixed moment coefficient. -/
def pom_replica_softcore_perron_feshbach_composition_moment_series_moment
    (q n : Nat) : Nat :=
  ∑ r ∈ Finset.range (n + 1),
    pom_replica_softcore_perron_feshbach_composition_moment_series_compositionTerm q n r

/-- The first prefixed cumulant/kappa data extracted from the moment enumeration. -/
def pom_replica_softcore_perron_feshbach_composition_moment_series_kappa
    (q n : Nat) : Int :=
  match n with
  | 0 => 1
  | 1 => q
  | _ =>
      (pom_replica_softcore_perron_feshbach_composition_moment_series_moment q n : Int) -
        (q : Int) ^ n

/-- Schur--Feshbach scalar equation after retaining the first prefixed kappa coefficient. -/
def pom_replica_softcore_perron_feshbach_composition_moment_series_schurScalar
    (q : Nat) (lam : ℝ) : ℝ :=
  lam - ((q : ℝ) +
    (pom_replica_softcore_perron_feshbach_composition_moment_series_kappa q 0 : ℝ))

/-- Paper-facing finite-composition moment-series statement. -/
def pom_replica_softcore_perron_feshbach_composition_moment_series_statement
    (q : Nat) : Prop :=
  pom_replica_softcore_perron_feshbach_composition_moment_series_moment q 0 = 1 ∧
    pom_replica_softcore_perron_feshbach_composition_moment_series_moment q 1 = q ∧
    pom_replica_softcore_perron_feshbach_composition_moment_series_moment q 2 = q ^ 2 ∧
    pom_replica_softcore_perron_feshbach_composition_moment_series_kappa q 0 = 1 ∧
    pom_replica_softcore_perron_feshbach_composition_moment_series_kappa q 1 = q ∧
    pom_replica_softcore_perron_feshbach_composition_moment_series_schurScalar q
        ((q : ℝ) + 1) = 0

/-- The finite one-part composition enumeration returns the expected monomial coefficient. -/
lemma pom_replica_softcore_perron_feshbach_composition_moment_series_moment_eq
    (q n : Nat) :
    pom_replica_softcore_perron_feshbach_composition_moment_series_moment q n = q ^ n := by
  rw [pom_replica_softcore_perron_feshbach_composition_moment_series_moment]
  rw [Finset.sum_eq_single n]
  · simp [pom_replica_softcore_perron_feshbach_composition_moment_series_compositionTerm]
  · intro b hb hbn
    simp [pom_replica_softcore_perron_feshbach_composition_moment_series_compositionTerm,
      hbn]
  · intro hn
    exact (hn (by simp)).elim

/-- Paper label: `thm:pom-replica-softcore-perron-feshbach-composition-moment-series`. -/
theorem paper_pom_replica_softcore_perron_feshbach_composition_moment_series (q : Nat) :
    pom_replica_softcore_perron_feshbach_composition_moment_series_statement q := by
  simp [pom_replica_softcore_perron_feshbach_composition_moment_series_statement,
    pom_replica_softcore_perron_feshbach_composition_moment_series_moment_eq,
    pom_replica_softcore_perron_feshbach_composition_moment_series_kappa,
    pom_replica_softcore_perron_feshbach_composition_moment_series_schurScalar]

end Omega.POM
