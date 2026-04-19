import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Concrete finite data for the Pick--Poisson near-collision certificate. The pairwise
pseudohyperbolic distances are indexed by a finite set of size `pairCount`, and the determinant
ratio is identified with the product of their squared distances. A distinguished index stores a
minimizing pair. -/
structure XiPickPoissonNearCollisionCertificateData where
  κ : ℕ
  pairCount : ℕ
  hpairCount : 2 * pairCount = κ * (κ - 1)
  pairDistance : Fin pairCount → ℕ
  minIndex : Fin pairCount
  detRatio : ℕ
  hFactorization :
    detRatio = ∏ i, (pairDistance i) ^ (2 : ℕ)
  hMin :
    ∀ i : Fin pairCount, pairDistance minIndex ≤ pairDistance i

/-- A powered near-collision certificate: some pairwise pseudohyperbolic distance, raised to the
full ordered-pair count, is bounded by the determinant ratio. -/
def XiPickPoissonNearCollisionCertificateData.existsNearCollisionWitness
    (D : XiPickPoissonNearCollisionCertificateData) : Prop :=
  ∃ i, (D.pairDistance i) ^ (D.κ * (D.κ - 1)) ≤ D.detRatio

/-- Paper wrapper for the Pick--Poisson near-collision certificate.
    cor:xi-pick-poisson-near-collision-certificate -/
theorem paper_xi_pick_poisson_near_collision_certificate
    (D : XiPickPoissonNearCollisionCertificateData) : D.existsNearCollisionWitness := by
  dsimp [XiPickPoissonNearCollisionCertificateData.existsNearCollisionWitness]
  refine ⟨D.minIndex, ?_⟩
  rw [D.hFactorization, ← D.hpairCount]
  have hpowBase :
      ((D.pairDistance D.minIndex) ^ (2 : ℕ)) ^ D.pairCount ≤
        ∏ i, (D.pairDistance i) ^ (2 : ℕ) := by
    simpa using
      (Finset.pow_card_le_prod (s := Finset.univ)
        (f := fun i => (D.pairDistance i) ^ (2 : ℕ))
        ((D.pairDistance D.minIndex) ^ (2 : ℕ))
        (fun i _ => by
          exact pow_le_pow_left' (D.hMin i) 2))
  have hpow :
      (D.pairDistance D.minIndex) ^ (2 * D.pairCount) ≤
        ∏ i, (D.pairDistance i) ^ (2 : ℕ) := by
    simpa [pow_mul] using hpowBase
  exact hpow
