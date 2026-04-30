import Omega.Zeta.SmithPrefixSufficiency

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-smith-local-zeta-shortest-prefix`.
The conclusion-level shortest-prefix statement is the existing Zeta Smith-prefix recovery and
singleton counterexample package, with the conclusion paper label. -/
theorem paper_conclusion_smith_local_zeta_shortest_prefix {m : ℕ} (e : Fin m → ℕ) :
    let E := Omega.Zeta.smithPrefixTop e
    (∀ k : ℕ, 1 ≤ k → k ≤ E →
      Omega.Zeta.smithPrefixValue e (k - 1) < Omega.Zeta.smithPrefixValue e k) ∧
    Omega.Zeta.smithPrefixValue e (E + 1) = Omega.Zeta.smithPrefixValue e E ∧
    (∀ ℓ : ℕ, 1 ≤ ℓ → ℓ < E →
      Omega.Zeta.smithPrefixMultiplicity e ℓ =
        2 * Omega.Zeta.smithPrefixValue e ℓ - Omega.Zeta.smithPrefixValue e (ℓ - 1) -
          Omega.Zeta.smithPrefixValue e (ℓ + 1)) ∧
    (1 ≤ E →
      Omega.Zeta.smithPrefixMultiplicity e E =
        Omega.Zeta.smithPrefixValue e E - Omega.Zeta.smithPrefixValue e (E - 1)) ∧
    (∀ k : ℕ, 1 ≤ k → k ≤ E →
      Omega.Zeta.smithPrefixValue (fun _ : Fin 1 => E) k =
        Omega.Zeta.smithPrefixValue (fun _ : Fin 1 => E + 1) k) ∧
    Omega.Zeta.smithPrefixValue (fun _ : Fin 1 => E) (E + 1) + 1 =
      Omega.Zeta.smithPrefixValue (fun _ : Fin 1 => E + 1) (E + 1) := by
  simpa using Omega.Zeta.paper_xi_smith_p_kernel_shortest_sufficient_prefix e

end Omega.Conclusion
