import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
import Mathlib.Topology.Order.Basic
import Omega.Conclusion.BoundaryStokesObservationMinimalDimension
import Omega.Conclusion.PrimeRegisterFiberCdimDensity

namespace Omega.Conclusion

open Filter
open scoped Topology

/-- The visible `H¹` rank tracked by the adelic Stokes package. -/
def adelicVisibleH1Rank (r : ℕ) : ℕ := r

/-- The torus rank extracted from the same adelic Stokes package. -/
def adelicTorusRank (r : ℕ) : ℕ := r

/-- The continuous `H¹` profile indexed by primes. -/
def adelicContinuousH1Dim (d : ℕ → ℕ) (p : ℕ) : ℕ := d p

/-- The mod-`p` quotient profile indexed by primes. -/
def adelicModpQuotientDim (d : ℕ → ℕ) (p : ℕ) : ℕ := d p

/-- Recovering the prime profile means the visible boundary data enforce the finite-generation
bound and the normalized circle-dimension profile agrees with the density profile. -/
def adelicStokesPrimeProfileRecovered
    (m n L : ℕ) (_f : Fin (2 ^ (m * n)) → Fin L) (s : ℕ → ℕ) : Prop :=
  2 ^ (m * n) ≤ L ∧
    primeFiberUpperCdim s = primeFiberUpperDensity s ∧
    primeFiberLowerCdim s = primeFiberLowerDensity s ∧
    ∃ ρ : ℝ, Tendsto (primeFiberCdimSeq s) atTop (𝓝 ρ)

/-- The adelic Stokes `H¹` rank matches the torus rank, the mod-`p` quotient dimensions recover
the continuous profile prime-by-prime, and the prime profile is recovered from the visible
boundary and circle-dimension data.
    thm:conclusion-adelic-stokes-h1-recovers-cdim-prime-profile -/
theorem paper_conclusion_adelic_stokes_h1_recovers_cdim_prime_profile
    (m n L visibleRank torusRank : ℕ)
    (f : Fin (2 ^ (m * n)) → Fin L) (hf : Function.Injective f)
    (s : ℕ → ℕ) (ρ : ℝ)
    (continuousH1Dim modpQuotientDim : ℕ → ℕ)
    (hρ : Tendsto (primeFiberDensitySeq s) atTop (𝓝 ρ))
    (hRank : visibleRank = torusRank)
    (hmodp : ∀ p, continuousH1Dim p = modpQuotientDim p) :
    adelicVisibleH1Rank visibleRank = adelicTorusRank torusRank ∧
      (∀ p, adelicContinuousH1Dim continuousH1Dim p =
        adelicModpQuotientDim modpQuotientDim p) ∧
      adelicStokesPrimeProfileRecovered m n L f s := by
  have hcdim :=
    paper_conclusion_prime_register_fiber_cdim_density s s ρ 0
      (by intro k; simp) hρ
  rcases hcdim with ⟨hupper, hlower, htendsto, _⟩
  have hfinite :
      2 ^ (m * n) ≤ L :=
    paper_conclusion_boundary_stokes_observation_minimal_dimension_seeds m n L f hf
  refine ⟨by simpa [adelicVisibleH1Rank, adelicTorusRank] using hRank, ?_, ?_⟩
  · intro p
    simpa [adelicContinuousH1Dim, adelicModpQuotientDim] using hmodp p
  · exact ⟨hfinite, hupper, hlower, ⟨ρ, htendsto⟩⟩

end Omega.Conclusion
