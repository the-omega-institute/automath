import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Omega.Zeta.FinitePrimeSupportThreewayCdimSplit

namespace Omega.Zeta

/-- The circle-dimension channel of finite localized integers is constantly equal to `1`, so no
uniform finite bound can recover arbitrarily large prime supports from it.
    thm:xi-localized-integers-no-uniform-finitely-generated-ledger -/
theorem paper_xi_localized_integers_no_uniform_finitely_generated_ledger :
    ¬ ∃ F : ℕ → ℕ, ∀ S : Omega.Zeta.FinitePrimeLocalization,
      S.card ≤ F (Omega.Zeta.localizedIntegersCircleDimension S) := by
  intro h
  rcases h with ⟨F, hF⟩
  let S : Omega.Zeta.FinitePrimeLocalization := Finset.range (F 1 + 1)
  have hdim : Omega.Zeta.localizedIntegersCircleDimension S = 1 :=
    (Omega.Zeta.paper_xi_finite_prime_support_threeway_cdim_split S).2.2
  have hbound : S.card ≤ F (Omega.Zeta.localizedIntegersCircleDimension S) := hF S
  have hsize : S.card = F 1 + 1 := by
    simp [S]
  have : F 1 + 1 ≤ F 1 := by
    simp [hdim, hsize] at hbound
  omega

end Omega.Zeta
