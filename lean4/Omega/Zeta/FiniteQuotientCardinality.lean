import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Pi

namespace Omega.Zeta.FiniteQuotientCardinality

/-- `|ZMod n| = n` for `n > 0`.
    prop:xi-cdim-finite-data-suffices -/
theorem card_zmod (n : ℕ) [NeZero n] :
    Fintype.card (ZMod n) = n :=
  ZMod.card n

/-- `|(Fin r → ZMod n)| = n^r` for `n > 0`.
    prop:xi-cdim-finite-data-suffices -/
theorem card_zmod_pi (r n : ℕ) [NeZero n] :
    Fintype.card (Fin r → ZMod n) = n ^ r := by
  rw [Fintype.card_fun, Fintype.card_fin, ZMod.card]

/-- Paper package: finite quotient free part cardinality.
    prop:xi-cdim-finite-data-suffices -/
theorem paper_xi_cdim_finite_quotient_free_part (r n : ℕ) [NeZero n] :
    Fintype.card (Fin r → ZMod n) = n ^ r :=
  card_zmod_pi r n

end Omega.Zeta.FiniteQuotientCardinality
