import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic

namespace Omega.Zeta

open Filter

/-- Concrete data for `prop:xi-poisson-kl-rate-implies-moment-cancellation`: a KL profile, its
centered moments, a sharp first-nonvanishing obstruction, and the even-moment delta criterion. -/
structure xi_poisson_kl_rate_implies_moment_cancellation_data where
  xi_poisson_kl_rate_implies_moment_cancellation_moment_ceiling : ℕ
  xi_poisson_kl_rate_implies_moment_cancellation_centered_moment : ℕ → ℝ
  xi_poisson_kl_rate_implies_moment_cancellation_kl_profile : ℝ → ℝ
  xi_poisson_kl_rate_implies_moment_cancellation_delta_at_center : Prop
  xi_poisson_kl_rate_implies_moment_cancellation_first_nonzero_obstruction :
    ∀ k : ℕ,
      1 ≤ k →
        xi_poisson_kl_rate_implies_moment_cancellation_centered_moment k ≠ 0 →
          (∀ j : ℕ,
            1 ≤ j →
              j < k →
                xi_poisson_kl_rate_implies_moment_cancellation_centered_moment j = 0) →
            ¬ Tendsto
              (fun t : ℝ =>
                t ^ (2 * k) * xi_poisson_kl_rate_implies_moment_cancellation_kl_profile t)
              atTop (nhds 0)
  xi_poisson_kl_rate_implies_moment_cancellation_even_moments_force_delta :
    (∀ r : ℕ,
      1 ≤ r →
        xi_poisson_kl_rate_implies_moment_cancellation_centered_moment (2 * r) = 0) →
      xi_poisson_kl_rate_implies_moment_cancellation_delta_at_center

namespace xi_poisson_kl_rate_implies_moment_cancellation_data

/-- Little-`o(t^{-2k})` is represented by the vanishing of the rescaled KL profile. -/
def xi_poisson_kl_rate_implies_moment_cancellation_little_o_at
    (D : xi_poisson_kl_rate_implies_moment_cancellation_data) (k : ℕ) : Prop :=
  Tendsto
    (fun t : ℝ =>
      t ^ (2 * k) * D.xi_poisson_kl_rate_implies_moment_cancellation_kl_profile t)
    atTop (nhds 0)

/-- The all-orders rate hypothesis used for the delta conclusion. -/
def xi_poisson_kl_rate_implies_moment_cancellation_all_orders_rate
    (D : xi_poisson_kl_rate_implies_moment_cancellation_data) : Prop :=
  ∀ k : ℕ,
    1 ≤ k → D.xi_poisson_kl_rate_implies_moment_cancellation_little_o_at k

private lemma xi_poisson_kl_rate_implies_moment_cancellation_finite_cancel
    (D : xi_poisson_kl_rate_implies_moment_cancellation_data)
    (hrate :
      ∀ k : ℕ,
        1 ≤ k →
          k ≤ D.xi_poisson_kl_rate_implies_moment_cancellation_moment_ceiling →
            D.xi_poisson_kl_rate_implies_moment_cancellation_little_o_at k) :
    ∀ k : ℕ,
      1 ≤ k →
        k ≤ D.xi_poisson_kl_rate_implies_moment_cancellation_moment_ceiling →
          D.xi_poisson_kl_rate_implies_moment_cancellation_centered_moment k = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro hk1 hkm
      by_contra hne
      have hprev :
          ∀ j : ℕ,
            1 ≤ j →
              j < k →
                D.xi_poisson_kl_rate_implies_moment_cancellation_centered_moment j = 0 := by
        intro j hj1 hjk
        exact ih j hjk hj1 (le_trans (Nat.le_of_lt hjk) hkm)
      exact
        (D.xi_poisson_kl_rate_implies_moment_cancellation_first_nonzero_obstruction
          k hk1 hne hprev) (hrate k hk1 hkm)

private lemma xi_poisson_kl_rate_implies_moment_cancellation_all_cancel
    (D : xi_poisson_kl_rate_implies_moment_cancellation_data)
    (hrate : D.xi_poisson_kl_rate_implies_moment_cancellation_all_orders_rate) :
    ∀ k : ℕ,
      1 ≤ k →
        D.xi_poisson_kl_rate_implies_moment_cancellation_centered_moment k = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro hk1
      by_contra hne
      have hprev :
          ∀ j : ℕ,
            1 ≤ j →
              j < k →
                D.xi_poisson_kl_rate_implies_moment_cancellation_centered_moment j = 0 := by
        intro j hj1 hjk
        exact ih j hjk hj1
      exact
        (D.xi_poisson_kl_rate_implies_moment_cancellation_first_nonzero_obstruction
          k hk1 hne hprev) (hrate k hk1)

/-- Concrete statement: a KL rate through order `m` cancels the first `m` centered moments; an
all-orders rate implies the supplied delta-at-center criterion. -/
def xi_poisson_kl_rate_implies_moment_cancellation_statement
    (D : xi_poisson_kl_rate_implies_moment_cancellation_data) : Prop :=
  ((∀ k : ℕ,
      1 ≤ k →
        k ≤ D.xi_poisson_kl_rate_implies_moment_cancellation_moment_ceiling →
          D.xi_poisson_kl_rate_implies_moment_cancellation_little_o_at k) →
    ∀ k : ℕ,
      1 ≤ k →
        k ≤ D.xi_poisson_kl_rate_implies_moment_cancellation_moment_ceiling →
          D.xi_poisson_kl_rate_implies_moment_cancellation_centered_moment k = 0) ∧
    (D.xi_poisson_kl_rate_implies_moment_cancellation_all_orders_rate →
      D.xi_poisson_kl_rate_implies_moment_cancellation_delta_at_center)

end xi_poisson_kl_rate_implies_moment_cancellation_data

open xi_poisson_kl_rate_implies_moment_cancellation_data

/-- Paper label: `prop:xi-poisson-kl-rate-implies-moment-cancellation`. -/
theorem paper_xi_poisson_kl_rate_implies_moment_cancellation
    (D : xi_poisson_kl_rate_implies_moment_cancellation_data) :
    xi_poisson_kl_rate_implies_moment_cancellation_statement D := by
  refine ⟨?_, ?_⟩
  · exact xi_poisson_kl_rate_implies_moment_cancellation_finite_cancel D
  · intro hrate
    apply D.xi_poisson_kl_rate_implies_moment_cancellation_even_moments_force_delta
    intro r hr
    exact xi_poisson_kl_rate_implies_moment_cancellation_all_cancel D hrate (2 * r) (by omega)

end Omega.Zeta
