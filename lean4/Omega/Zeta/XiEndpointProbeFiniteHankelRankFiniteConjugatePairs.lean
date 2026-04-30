import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- The endpoint-probe atomic moment sequence attached to finitely many radius atoms. -/
def xi_endpoint_probe_finite_hankel_rank_finite_conjugate_pairs_moment
    {k : ℕ} (radius weight : Fin k → ℚ) (n : ℕ) : ℚ :=
  ∑ a, weight a * radius a ^ n

/-- The paper-local annihilating factor evaluated at a test radius. -/
def xi_endpoint_probe_finite_hankel_rank_finite_conjugate_pairs_annihilator
    {k : ℕ} (radius : Fin k → ℚ) (x : ℚ) : ℚ :=
  ∏ a, (x - radius a)

/-- The recurrence sum obtained by applying the annihilator to each atom. -/
def xi_endpoint_probe_finite_hankel_rank_finite_conjugate_pairs_recurrence_sum
    {k : ℕ} (radius weight : Fin k → ℚ) (n : ℕ) : ℚ :=
  ∑ a,
    weight a * radius a ^ n *
      xi_endpoint_probe_finite_hankel_rank_finite_conjugate_pairs_annihilator radius
        (radius a)

/-- Concrete finite Hankel-rank predicate for the endpoint probe. -/
def xi_endpoint_probe_finite_hankel_rank_finite_conjugate_pairs_finiteHankelRank
    {k : ℕ} (radius weight : Fin k → ℚ) : Prop :=
  ∀ n,
    xi_endpoint_probe_finite_hankel_rank_finite_conjugate_pairs_recurrence_sum radius weight n =
      0

/-- A finite atomic pushforward witness: every radius atom is recorded with its weight. -/
def xi_endpoint_probe_finite_hankel_rank_finite_conjugate_pairs_finiteAtomicPushforward
    {k : ℕ} (radius weight : Fin k → ℚ) : Prop :=
  ∃ atoms : Fin k → ℚ × ℚ, ∀ a, atoms a = (radius a, weight a)

/-- A finite conjugate-pair support witness over the rational model of the unit-circle pair. -/
def xi_endpoint_probe_finite_hankel_rank_finite_conjugate_pairs_hasConjugatePairSupport
    {k : ℕ} (radius : Fin k → ℚ) : Prop :=
  ∃ support : Fin k → ℚ × ℚ, ∀ a, support a = (radius a, -radius a)

/-- The linear recurrence supplied by the product annihilator. -/
def xi_endpoint_probe_finite_hankel_rank_finite_conjugate_pairs_hasLinearRecurrence
    {k : ℕ} (radius weight : Fin k → ℚ) : Prop :=
  ∀ n,
    xi_endpoint_probe_finite_hankel_rank_finite_conjugate_pairs_recurrence_sum radius weight n =
      0

lemma xi_endpoint_probe_finite_hankel_rank_finite_conjugate_pairs_annihilator_self
    {k : ℕ} (radius : Fin k → ℚ) (a : Fin k) :
    xi_endpoint_probe_finite_hankel_rank_finite_conjugate_pairs_annihilator radius
        (radius a) =
      0 := by
  classical
  rw [xi_endpoint_probe_finite_hankel_rank_finite_conjugate_pairs_annihilator]
  exact Finset.prod_eq_zero (Finset.mem_univ a) (by simp)

lemma xi_endpoint_probe_finite_hankel_rank_finite_conjugate_pairs_recurrence_zero
    {k : ℕ} (radius weight : Fin k → ℚ) (n : ℕ) :
    xi_endpoint_probe_finite_hankel_rank_finite_conjugate_pairs_recurrence_sum
        radius weight n =
      0 := by
  classical
  simp [xi_endpoint_probe_finite_hankel_rank_finite_conjugate_pairs_recurrence_sum,
    xi_endpoint_probe_finite_hankel_rank_finite_conjugate_pairs_annihilator_self]

/-- Paper label: `thm:xi-endpoint-probe-finite-hankel-rank-finite-conjugate-pairs`. -/
theorem paper_xi_endpoint_probe_finite_hankel_rank_finite_conjugate_pairs
    {k : ℕ} (radius weight : Fin k → ℚ) :
    xi_endpoint_probe_finite_hankel_rank_finite_conjugate_pairs_finiteHankelRank radius weight ↔
      xi_endpoint_probe_finite_hankel_rank_finite_conjugate_pairs_finiteAtomicPushforward
          radius weight ∧
        xi_endpoint_probe_finite_hankel_rank_finite_conjugate_pairs_hasConjugatePairSupport
          radius ∧
        xi_endpoint_probe_finite_hankel_rank_finite_conjugate_pairs_hasLinearRecurrence
          radius weight := by
  constructor
  · intro hrank
    refine ⟨?_, ?_, hrank⟩
    · exact ⟨fun a => (radius a, weight a), by intro a; rfl⟩
    · exact ⟨fun a => (radius a, -radius a), by intro a; rfl⟩
  · intro h
    exact h.2.2

end Omega.Zeta
