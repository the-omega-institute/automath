import Omega.Zeta.SmithPrefixSufficiency

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-smith-local-zeta-complete-invariant`. -/
theorem paper_conclusion_smith_local_zeta_complete_invariant {m : ℕ} (e e' : Fin m → ℕ)
    (hcoeff : ∀ k : ℕ, Omega.Zeta.smithPrefixValue e k =
      Omega.Zeta.smithPrefixValue e' k) :
    ∀ ℓ : ℕ, Omega.Zeta.smithPrefixMultiplicity e ℓ =
      Omega.Zeta.smithPrefixMultiplicity e' ℓ := by
  have hdelta :
      ∀ k : ℕ, Omega.Zeta.smithPrefixDelta e k = Omega.Zeta.smithPrefixDelta e' k := by
    intro k
    cases k with
    | zero =>
        unfold Omega.Zeta.smithPrefixDelta
        simp
    | succ k =>
        rw [Omega.Zeta.smithPrefixDelta_eq_sub e k,
          Omega.Zeta.smithPrefixDelta_eq_sub e' k, hcoeff (k + 1), hcoeff k]
  intro ℓ
  rw [Omega.Zeta.smithPrefixMultiplicity_eq_delta_sub_delta e ℓ,
    Omega.Zeta.smithPrefixMultiplicity_eq_delta_sub_delta e' ℓ, hdelta ℓ, hdelta (ℓ + 1)]

end Omega.Conclusion
