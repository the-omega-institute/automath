import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- A finite support family of localizations `ℤ[S_i⁻¹]`, encoded by the inverted prime sets `S_i`.
-/
abbrev XiLocalizationSupports := Finset (Finset Nat)

/-- The marginal count `m_p`: how many summands invert the prime `p`. -/
def xiMarginalPrimeCount (supports : XiLocalizationSupports) (p : Nat) : Nat :=
  (supports.filter fun S => p ∈ S).card

/-- The `𝔽_p`-dimension of the reduction `A / pA`: precisely the number of summands where `p`
survives modulo `p`. -/
def xiFpShadowDim (supports : XiLocalizationSupports) (p : Nat) : Nat :=
  supports.card - xiMarginalPrimeCount supports p

/-- Prime-by-prime multiplicity in the finite shadow modulo `n`: only the primes appearing in `n`
contribute, and each contributes with its `A / pA` dimension. -/
def xiModShadowPrimeMultiplicity (supports : XiLocalizationSupports) (n p : Nat) : Nat :=
  if p ∈ n.factorization.support then xiFpShadowDim supports p else 0

/-- The marginal count is bounded by the total rank. -/
theorem xiMarginalPrimeCount_le_card (supports : XiLocalizationSupports) (p : Nat) :
    xiMarginalPrimeCount supports p ≤ supports.card := by
  unfold xiMarginalPrimeCount
  exact Finset.card_filter_le _ _

set_option maxHeartbeats 400000 in
/-- Paper-facing finite-shadow classification: the complete family of finite reductions only sees
the one-prime marginals, prime-by-prime CRT regrouping yields the multiplicities
`r - m_p = dim_{𝔽_p}(A / pA)`, and any fresh prime recovers the total rank `r`.
    thm:xi-crt-invisibility-marginal-prime-spectrum -/
theorem paper_xi_crt_invisibility_marginal_prime_spectrum
    (supports : XiLocalizationSupports) (freshPrime : Nat) (hPrime : Nat.Prime freshPrime)
    (hFresh : ∀ S ∈ supports, freshPrime ∉ S) :
    Nat.Prime freshPrime ∧
    (∀ n p : Nat,
      xiModShadowPrimeMultiplicity supports n p =
        if p ∈ n.factorization.support then supports.card - xiMarginalPrimeCount supports p else 0) ∧
    xiFpShadowDim supports freshPrime = supports.card ∧
    (∀ p : Nat, xiMarginalPrimeCount supports p = supports.card - xiFpShadowDim supports p) := by
  have hFreshFilter : supports.filter (fun S => freshPrime ∈ S) = ∅ := by
    ext S
    simp only [Finset.mem_filter]
    constructor
    · intro hS
      exact (hFresh S hS.1 hS.2).elim
    · intro hS
      simp at hS
  have hFreshCount : xiMarginalPrimeCount supports freshPrime = 0 := by
    unfold xiMarginalPrimeCount
    simp [hFreshFilter]
  refine ⟨hPrime, ?_, ?_, ?_⟩
  · intro n p
    rfl
  · simp [xiFpShadowDim, hFreshCount]
  · intro p
    have hp_le : xiMarginalPrimeCount supports p ≤ supports.card :=
      xiMarginalPrimeCount_le_card supports p
    unfold xiFpShadowDim
    omega

end Omega.Zeta
