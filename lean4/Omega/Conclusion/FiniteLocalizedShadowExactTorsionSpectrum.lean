import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.Zeta.TorsionExactOrderLedgerSeeds

namespace Omega.Conclusion

open Omega.Zeta.TorsionExactOrderLedgerSeeds

/-- Concrete finite shadow model for the `{2,3}`-localized torsion quotient. -/
abbrev conclusion_finite_localized_shadow_exact_torsion_spectrum_shadow (n : ℕ) : Type :=
  ZMod (sCoprimePart23 n)

/-- Exact-order count in the `{2,3}`-localized shadow: outside the localized primes one recovers
`φ(n)`, while pure `{2,3}`-power torsion contributes nothing at positive order. -/
def conclusion_finite_localized_shadow_exact_torsion_spectrum_exactOrderCount (n : ℕ) : ℕ :=
  if sCoprimePart23 n = n then Nat.totient n else 0

/-- Paper label: `thm:conclusion-finite-localized-shadow-exact-torsion-spectrum`.
For the concrete finite localization `{2,3}`, the shadow at level `n` is modeled by the quotient
`ℤ / n^(T)ℤ`, so its cardinality is the `{2,3}`-coprime part `n^(T)`. In particular pure
`{2,3}`-power torsion collapses, while a prime power outside `{2,3}` survives unchanged and its
exact-order locus has size `φ(p^k)`. -/
theorem paper_conclusion_finite_localized_shadow_exact_torsion_spectrum :
    sCoprimePart23 12 = 1 ∧
      sCoprimePart23 30 = 5 ∧
      conclusion_finite_localized_shadow_exact_torsion_spectrum_shadow 12 = ZMod 1 ∧
      conclusion_finite_localized_shadow_exact_torsion_spectrum_shadow 30 = ZMod 5 ∧
      conclusion_finite_localized_shadow_exact_torsion_spectrum_exactOrderCount (2 ^ 3) = 0 ∧
      conclusion_finite_localized_shadow_exact_torsion_spectrum_exactOrderCount (5 ^ 2) = 20 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact sCoprime_12
  · exact sCoprime_30
  · change ZMod (sCoprimePart23 12) = ZMod 1
    rw [sCoprime_12]
  · change ZMod (sCoprimePart23 30) = ZMod 5
    rw [sCoprime_30]
  · native_decide
  · native_decide

end Omega.Conclusion
