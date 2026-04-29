import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete finite-prefix rank package for faithful prime-ledger semantics. The function
`requiredRank k` records the rank forced by the first `k` independent prime-register axes. -/
structure xi_infinite_depth_prime_ledger_infinite_rank_obstruction_data where
  xi_infinite_depth_prime_ledger_infinite_rank_obstruction_requiredRank : ℕ → ℕ
  xi_infinite_depth_prime_ledger_infinite_rank_obstruction_prefix_rank_lower_bound :
    ∀ k : ℕ,
      k ≤ xi_infinite_depth_prime_ledger_infinite_rank_obstruction_requiredRank k

namespace xi_infinite_depth_prime_ledger_infinite_rank_obstruction_data

/-- No single finite generator rank can faithfully realize all finite prime-register prefixes. -/
def noFiniteGeneratedFaithfulLedger
    (D : xi_infinite_depth_prime_ledger_infinite_rank_obstruction_data) : Prop :=
  ¬ ∃ r : ℕ,
    ∀ k : ℕ,
      D.xi_infinite_depth_prime_ledger_infinite_rank_obstruction_requiredRank k ≤ r

end xi_infinite_depth_prime_ledger_infinite_rank_obstruction_data

/-- Paper label: `thm:xi-infinite-depth-prime-ledger-infinite-rank-obstruction`. -/
theorem paper_xi_infinite_depth_prime_ledger_infinite_rank_obstruction
    (D : xi_infinite_depth_prime_ledger_infinite_rank_obstruction_data) :
    D.noFiniteGeneratedFaithfulLedger := by
  rintro ⟨r, hr⟩
  have hlower :
      r + 1 ≤
        D.xi_infinite_depth_prime_ledger_infinite_rank_obstruction_requiredRank (r + 1) :=
    D.xi_infinite_depth_prime_ledger_infinite_rank_obstruction_prefix_rank_lower_bound (r + 1)
  have hupper :
      D.xi_infinite_depth_prime_ledger_infinite_rank_obstruction_requiredRank (r + 1) ≤ r :=
    hr (r + 1)
  exact Nat.not_succ_le_self r (Nat.le_trans hlower hupper)

end Omega.Zeta
