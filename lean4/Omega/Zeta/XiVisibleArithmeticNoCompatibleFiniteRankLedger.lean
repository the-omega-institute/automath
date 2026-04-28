import Mathlib.Tactic
import Omega.Folding.KilloPrimeFreedomNonFinitizability

namespace Omega.Zeta

/-- The finite-rank target for a visible arithmetic ledger with `k` additive coordinates. -/
abbrev xi_visible_arithmetic_no_compatible_finite_rank_ledger_target (k : ℕ) :=
  Omega.Folding.KilloFiniteRegister k

/-- The stabilized source window containing the first `k + 1` prime directions. -/
abbrev xi_visible_arithmetic_no_compatible_finite_rank_ledger_source (k : ℕ) :=
  Omega.Folding.KilloPrimeWindow k

/-- The stable map extracted from a compatible family of finite-resolution ledgers. -/
abbrev xi_visible_arithmetic_no_compatible_finite_rank_ledger_stable_map (k : ℕ) :=
  xi_visible_arithmetic_no_compatible_finite_rank_ledger_source k →ₗ[ℚ]
    xi_visible_arithmetic_no_compatible_finite_rank_ledger_target k

/-- The stable ledger separates the visible prime-window states. -/
def xi_visible_arithmetic_no_compatible_finite_rank_ledger_stable_map_injective
    {k : ℕ}
    (Φ : xi_visible_arithmetic_no_compatible_finite_rank_ledger_stable_map k) : Prop :=
  Function.Injective Φ

/-- Linearity records the multiplicative-to-additive ledger law after stabilization. -/
def xi_visible_arithmetic_no_compatible_finite_rank_ledger_stable_map_additive
    {k : ℕ}
    (Φ : xi_visible_arithmetic_no_compatible_finite_rank_ledger_stable_map k) : Prop :=
  ∀ x y, Φ (x + y) = Φ x + Φ y

/-- A compatible finite-rank visible ledger would give an injective stable additive map on every
finite prime window. -/
def xi_visible_arithmetic_no_compatible_finite_rank_ledger_compatible
    (k : ℕ) : Prop :=
  ∃ Φ : xi_visible_arithmetic_no_compatible_finite_rank_ledger_stable_map k,
    xi_visible_arithmetic_no_compatible_finite_rank_ledger_stable_map_injective Φ ∧
      xi_visible_arithmetic_no_compatible_finite_rank_ledger_stable_map_additive Φ

/-- Paper-facing statement: every finite-rank stable ledger is obstructed on its next prime
window. -/
def xi_visible_arithmetic_no_compatible_finite_rank_ledger_statement : Prop :=
  ∀ k : ℕ, ¬ xi_visible_arithmetic_no_compatible_finite_rank_ledger_compatible k

/-- Paper label: `thm:xi-visible-arithmetic-no-compatible-finite-rank-ledger`. -/
theorem paper_xi_visible_arithmetic_no_compatible_finite_rank_ledger :
    xi_visible_arithmetic_no_compatible_finite_rank_ledger_statement := by
  intro k h
  rcases h with ⟨Φ, hΦ, _hadd⟩
  exact (Omega.Folding.paper_killo_prime_freedom_non_finitizability.2 k) ⟨Φ, hΦ⟩

end Omega.Zeta
