import Mathlib

namespace Omega.Zeta

/-- Finite `b`-bit windows on an `r`-channel visible lattice, with a torsion register of size
`torsionCard`. -/
abbrev XiCdimWindow (r b torsionCard : ℕ) :=
  (Fin r → Fin (2 ^ b)) × Fin torsionCard

/-- The visible phase alphabet carried by the `k` explicit channels. -/
abbrev XiCdimVisiblePhaseAlphabet (k b : ℕ) :=
  Fin k → Fin (2 ^ b)

/-- Cardinality of the finite window used in the residual-gap count. -/
def xiCdimWindowCard (r b torsionCard : ℕ) : ℕ :=
  Fintype.card (XiCdimWindow r b torsionCard)

/-- Cardinality of the visible phase alphabet. -/
def xiCdimVisiblePhaseCard (k b : ℕ) : ℕ :=
  Fintype.card (XiCdimVisiblePhaseAlphabet k b)

lemma xiCdimWindowCard_eq (r b torsionCard : ℕ) :
    xiCdimWindowCard r b torsionCard = (2 ^ b) ^ r * torsionCard := by
  simp [xiCdimWindowCard, XiCdimWindow]

lemma xiCdimVisiblePhaseCard_eq (k b : ℕ) :
    xiCdimVisiblePhaseCard k b = (2 ^ b) ^ k := by
  simp [xiCdimVisiblePhaseCard, XiCdimVisiblePhaseAlphabet]

/-- Paper label: `thm:xi-cdim-kolm-residual-gap`.

If the visible phase channel exposes only `k ≤ r` of the `r` `b`-bit coordinates, then the number
of states that can be paired with a short residual description is bounded by the visible alphabet
size times the short-description budget. The cardinality comparison packages the finite window,
visible alphabet, and residual register into the multiplicative exceptional-set bound. -/
theorem paper_xi_cdim_kolm_residual_gap
    (r k b torsionCard shortCodeCount t : ℕ)
    (hk : k ≤ r)
    (hshort : shortCodeCount * 2 ^ t ≤ (2 ^ b) ^ (r - k) * torsionCard) :
    let W := xiCdimWindowCard r b torsionCard
    let P := xiCdimVisiblePhaseCard k b
    P * shortCodeCount * 2 ^ t ≤ W ∧
      W = P * ((2 ^ b) ^ (r - k) * torsionCard) := by
  dsimp
  have hcard :
      xiCdimWindowCard r b torsionCard =
        xiCdimVisiblePhaseCard k b * ((2 ^ b) ^ (r - k) * torsionCard) := by
    rw [xiCdimWindowCard_eq, xiCdimVisiblePhaseCard_eq]
    calc
      (2 ^ b) ^ r * torsionCard = (2 ^ b) ^ (k + (r - k)) * torsionCard := by
        rw [Nat.add_sub_of_le hk]
      _ = ((2 ^ b) ^ k * (2 ^ b) ^ (r - k)) * torsionCard := by
        rw [pow_add]
      _ = (2 ^ b) ^ k * ((2 ^ b) ^ (r - k) * torsionCard) := by
        rw [mul_assoc]
  have hbound :
      xiCdimVisiblePhaseCard k b * shortCodeCount * 2 ^ t ≤
        xiCdimVisiblePhaseCard k b * ((2 ^ b) ^ (r - k) * torsionCard) := by
    simpa [Nat.mul_assoc] using Nat.mul_le_mul_left (xiCdimVisiblePhaseCard k b) hshort
  exact ⟨by simpa [hcard] using hbound, hcard⟩

end Omega.Zeta
