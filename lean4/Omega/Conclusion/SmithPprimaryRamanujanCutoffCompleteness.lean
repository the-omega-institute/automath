import Omega.Zeta.SmithPrefixSufficiency

namespace Omega.Conclusion

open Omega.Zeta

/-- Paper-facing cutoff package for the p-primary Smith/Ramanujan shadow: below the top exponent
the singleton witnesses `E` and `E + 1` are indistinguishable from the truncated prefix data,
while at and below the cutoff the exact multiplicities are recovered by finite differences.
    thm:conclusion-smith-pprimary-ramanujan-cutoff-completeness -/
theorem paper_conclusion_smith_pprimary_ramanujan_cutoff_completeness {m : ℕ} (e : Fin m → ℕ) :
    let E := smithPrefixTop e
    (∀ k : ℕ, 1 ≤ k → k ≤ E →
      smithPrefixValue (fun _ : Fin 1 => E) k =
        smithPrefixValue (fun _ : Fin 1 => E + 1) k) ∧
    smithPrefixValue (fun _ : Fin 1 => E) (E + 1) + 1 =
      smithPrefixValue (fun _ : Fin 1 => E + 1) (E + 1) ∧
    (∀ ℓ : ℕ, 1 ≤ ℓ → ℓ < E →
      smithPrefixMultiplicity e ℓ =
        2 * smithPrefixValue e ℓ - smithPrefixValue e (ℓ - 1) - smithPrefixValue e (ℓ + 1)) ∧
    (1 ≤ E → smithPrefixMultiplicity e E = smithPrefixValue e E - smithPrefixValue e (E - 1)) :=
by
  dsimp
  rcases paper_xi_smith_p_kernel_shortest_sufficient_prefix e with
    ⟨_, _, hrecover, htop, hshadow, hseparate⟩
  exact ⟨hshadow, hseparate, hrecover, htop⟩

end Omega.Conclusion
