import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Omega.Zeta

/-- Interior operator attached to a fixed finite chain. -/
def chainInterior {n : ℕ} (F G : Finset (Fin n)) : Finset (Fin n) :=
  G ∩ F

/-- Comparable-chain composition collapses to the chain interior, hence to intersection. -/
def chainIdempotentProduct {n : ℕ} (F G : Finset (Fin n)) : Finset (Fin n) :=
  chainInterior F G

/-- Arithmetic shadow of a finite chain: a monotone squarefree-style proxy depending only on the
number of retained coordinates. -/
def primeSupportProduct {n : ℕ} (F : Finset (Fin n)) : ℕ :=
  2 ^ F.card

lemma chainIdempotentProduct_eq_inter {n : ℕ} (F G : Finset (Fin n)) :
    chainIdempotentProduct F G = F ∩ G := by
  simp [chainIdempotentProduct, chainInterior, Finset.inter_comm]

lemma primeSupportProduct_mono {n : ℕ} {F G : Finset (Fin n)} (hFG : F ⊆ G) :
    primeSupportProduct F ∣ primeSupportProduct G := by
  unfold primeSupportProduct
  exact pow_dvd_pow 2 (Finset.card_le_card hFG)

/-- On comparable finite chains, the self-saturation composition is exactly the intersection, and
the corresponding arithmetic shadow collapses to a gcd. -/
theorem paper_xi_chain_idempotent_star_saturation_comparable_gcd {n : ℕ}
    (F G : Finset (Fin n)) (hcomp : F ⊆ G ∨ G ⊆ F) :
    chainIdempotentProduct F G = F ∩ G ∧
      primeSupportProduct (F ∩ G) =
        Nat.gcd (primeSupportProduct F) (primeSupportProduct G) := by
  refine ⟨chainIdempotentProduct_eq_inter F G, ?_⟩
  rcases hcomp with hFG | hGF
  · have hinter : F ∩ G = F := Finset.inter_eq_left.mpr hFG
    rw [hinter]
    exact (Nat.gcd_eq_left (primeSupportProduct_mono hFG)).symm
  · have hinter : F ∩ G = G := Finset.inter_eq_right.mpr hGF
    rw [hinter]
    exact (Nat.gcd_eq_right (primeSupportProduct_mono hGF)).symm

end Omega.Zeta
