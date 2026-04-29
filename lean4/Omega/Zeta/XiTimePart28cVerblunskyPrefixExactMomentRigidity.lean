import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part28c-verblunsky-prefix-exact-moment-rigidity`.
Finite CMV locality propagates prefix agreement at depth `2 * m + 1` to all moment
agreements of order at most `m`. -/
theorem paper_xi_time_part28c_verblunsky_prefix_exact_moment_rigidity
    (PrefixAgree MomentAgree : ℕ → Prop) (m : ℕ)
    (hmono : ∀ {n k : ℕ}, n ≤ k → PrefixAgree k → PrefixAgree n)
    (hlocal : ∀ r : ℕ, r ≤ m → PrefixAgree (2 * r + 1) → MomentAgree r)
    (hprefix : PrefixAgree (2 * m + 1)) :
    ∀ r : ℕ, r ≤ m → MomentAgree r := by
  intro r hr
  exact hlocal r hr (hmono (by omega) hprefix)

end Omega.Zeta
