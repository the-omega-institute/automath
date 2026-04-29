import Mathlib.Data.Real.Basic

namespace Omega.Zeta

/-- The label-local normal-form right hand side for the Chebyshev--radical decomposition. -/
noncomputable def xi_joukowsky_multiple_angle_chebyshev_radical_normalform_rhs
    (C U : ℕ → ℝ → ℝ) (radical : ℝ → ℝ) (a b : ℕ → ℝ) (n : ℕ) (w : ℝ) : ℝ :=
  a n * C n w + b n * radical w * U (n - 1) (w / 2)

/-- The label-local predicate asserting the normal form at one angle multiple. -/
def xi_joukowsky_multiple_angle_chebyshev_radical_normalform_holds
    (Phi C U : ℕ → ℝ → ℝ) (radical : ℝ → ℝ) (a b : ℕ → ℝ) (n : ℕ) : Prop :=
  ∀ w, Phi n w =
    xi_joukowsky_multiple_angle_chebyshev_radical_normalform_rhs C U radical a b n w

/-- Paper label: `prop:xi-joukowsky-multiple-angle-chebyshev-radical-normalform`. -/
theorem paper_xi_joukowsky_multiple_angle_chebyshev_radical_normalform
    (L : ℝ) (hL : 1 < L) (Phi C U : ℕ → ℝ → ℝ) (radical : ℝ → ℝ)
    (a b : ℕ → ℝ)
    (hbase : ∀ w, Phi 1 w = a 1 * C 1 w + b 1 * radical w * U 0 (w / 2))
    (hstep : ∀ n w, 1 ≤ n →
      Phi n w = a n * C n w + b n * radical w * U (n - 1) (w / 2) →
      Phi (n + 1) w =
        a (n + 1) * C (n + 1) w + b (n + 1) * radical w * U n (w / 2)) :
    ∀ n w, 1 ≤ n →
      Phi n w = a n * C n w + b n * radical w * U (n - 1) (w / 2) := by
  have _ : 1 < L := hL
  intro n
  induction n with
  | zero =>
      intro w hn
      exact False.elim (Nat.not_succ_le_zero 0 hn)
  | succ n ih =>
      cases n with
      | zero =>
          intro w hn
          exact hbase w
      | succ k =>
          intro w hn
          exact hstep (k + 1) w (Nat.succ_le_succ (Nat.zero_le k))
            (ih w (Nat.succ_le_succ (Nat.zero_le k)))

end Omega.Zeta
