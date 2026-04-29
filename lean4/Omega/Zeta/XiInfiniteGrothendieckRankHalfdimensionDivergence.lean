import Mathlib.Data.Finsupp.Basic
import Mathlib.Tactic
import Omega.CircleDimension.ImplementationStructuralHalfCircleDimension
import Omega.Folding.KilloPrimeFreedomNonFinitizability

namespace Omega.Zeta

/-- The countable cancellative prime-register monoid used in the `xi` half-dimension comparison. -/
abbrev xi_infinite_grothendieck_rank_halfdimension_divergence_prime_monoid := ℕ →₀ ℕ

/-- Its Grothendieck completion is the free abelian group on countably many prime axes. -/
abbrev xi_infinite_grothendieck_rank_halfdimension_divergence_completion := ℕ →₀ ℤ

/-- The finite rational host of homological half-circle dimension `k`. -/
abbrev xi_infinite_grothendieck_rank_halfdimension_divergence_finite_host (k : ℕ) :=
  Omega.Folding.KilloFiniteRegister k

/-- Homological finite-dimensional realizations are obstructed at every finite rank. -/
def xi_infinite_grothendieck_rank_halfdimension_divergence_homHalfCircleDimInfinite : Prop :=
  ∀ k : ℕ, Omega.Folding.killoFiniteRegisterLinearizationObstructed k

/-- The implementation layer still has the canonical countable injection and half-circle dimension
`1/2`. -/
def xi_infinite_grothendieck_rank_halfdimension_divergence_implCircleDimHalf : Prop :=
  Function.Injective
      Omega.CircleDimension.killo_implementation_vs_structural_half_circle_dimension_impl_embedding ∧
    Omega.CircleDimension.killo_implementation_vs_structural_half_circle_dimension_impl_dim =
      (1 : ℚ) / (2 : ℚ)

/-- Paper label: `thm:xi-infinite-grothendieck-rank-halfdimension-divergence`.

Every finite homological embedding would restrict to an injection from the first `k + 1`
Grothendieck prime axes into a rank-`k` rational host, contradicting rank.  The implementation
side is the already-verified canonical countable embedding with half-circle dimension `1/2`. -/
theorem paper_xi_infinite_grothendieck_rank_halfdimension_divergence :
    xi_infinite_grothendieck_rank_halfdimension_divergence_homHalfCircleDimInfinite ∧
      xi_infinite_grothendieck_rank_halfdimension_divergence_implCircleDimHalf := by
  refine ⟨?_, ?_⟩
  · exact Omega.Folding.paper_killo_prime_freedom_non_finitizability.2
  · exact
      ⟨Omega.CircleDimension.paper_killo_implementation_vs_structural_half_circle_dimension.2.2.1,
        Omega.CircleDimension.paper_killo_implementation_vs_structural_half_circle_dimension.2.2.2⟩

end Omega.Zeta
