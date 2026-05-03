import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label:
`thm:xi-time-part9zn-window6-pushforward-equivariant-quadratic-scalar-rigidity`.
The scalar-commutant hypothesis applies directly to any operator commuting with all six
pushforward generators. -/
theorem paper_xi_time_part9zn_window6_pushforward_equivariant_quadratic_scalar_rigidity
    {V : Type*} [SMul Complex V] (L : Fin 6 → V → V) (Sigma : V → V)
    (hcommutant_scalar :
      ∀ T : V → V, (∀ i x, T (L i x) = L i (T x)) → ∃ c : Complex, ∀ x, T x = c • x)
    (hSigma : ∀ i x, Sigma (L i x) = L i (Sigma x)) :
    ∃ c : Complex, ∀ x, Sigma x = c • x := by
  exact hcommutant_scalar Sigma hSigma

end Omega.Zeta
