import Mathlib.Tactic
import Omega.Zeta.XiChainIdempotentStarSaturationComparableGcd

namespace Omega.Zeta

/-- Paper label: `cor:xi-chain-idempotent-comparable-finite-gcd-collapse`. -/
theorem paper_xi_chain_idempotent_comparable_finite_gcd_collapse {n : Nat}
    (F0 : Finset (Fin n)) (Fs : List (Finset (Fin n)))
    (hchain : ∀ G ∈ F0 :: Fs, ∀ H ∈ F0 :: Fs, G ⊆ H ∨ H ⊆ G) :
    Fs.foldl Omega.Zeta.chainIdempotentProduct F0 = Fs.foldl (fun A B => A ∩ B) F0 ∧
      Omega.Zeta.primeSupportProduct
          (Fs.foldl Omega.Zeta.chainIdempotentProduct F0) =
        (Fs.map Omega.Zeta.primeSupportProduct).foldl Nat.gcd
          (Omega.Zeta.primeSupportProduct F0) := by
  induction Fs generalizing F0 with
  | nil =>
      simp
  | cons B Bs ih =>
      have hcomp : F0 ⊆ B ∨ B ⊆ F0 := hchain F0 (by simp) B (by simp)
      have hbinary :=
        paper_xi_chain_idempotent_star_saturation_comparable_gcd F0 B hcomp
      have htail :
          ∀ G ∈ (F0 ∩ B) :: Bs, ∀ H ∈ (F0 ∩ B) :: Bs, G ⊆ H ∨ H ⊆ G := by
        rcases hcomp with hF0B | hBF0
        · have hinter : F0 ∩ B = F0 := Finset.inter_eq_left.mpr hF0B
          intro G hG H hH
          rw [hinter] at hG hH
          exact hchain G (by
            simp only [List.mem_cons] at hG ⊢
            rcases hG with rfl | hG
            · exact Or.inl rfl
            · exact Or.inr (Or.inr hG)) H (by
            simp only [List.mem_cons] at hH ⊢
            rcases hH with rfl | hH
            · exact Or.inl rfl
            · exact Or.inr (Or.inr hH))
        · have hinter : F0 ∩ B = B := Finset.inter_eq_right.mpr hBF0
          intro G hG H hH
          rw [hinter] at hG hH
          exact hchain G (by
            simp only [List.mem_cons] at hG ⊢
            rcases hG with rfl | hG
            · exact Or.inr (Or.inl rfl)
            · exact Or.inr (Or.inr hG)) H (by
            simp only [List.mem_cons] at hH ⊢
            rcases hH with rfl | hH
            · exact Or.inr (Or.inl rfl)
            · exact Or.inr (Or.inr hH))
      have hih := ih (F0 := F0 ∩ B) htail
      constructor
      · simpa [chainIdempotentProduct_eq_inter F0 B] using hih.1
      · calc
          primeSupportProduct ((B :: Bs).foldl chainIdempotentProduct F0)
              = primeSupportProduct (Bs.foldl chainIdempotentProduct (F0 ∩ B)) := by
                simp [chainIdempotentProduct_eq_inter F0 B]
          _ = (Bs.map primeSupportProduct).foldl Nat.gcd
              (primeSupportProduct (F0 ∩ B)) := hih.2
          _ = (Bs.map primeSupportProduct).foldl Nat.gcd
              (Nat.gcd (primeSupportProduct F0) (primeSupportProduct B)) := by
                rw [hbinary.2]
          _ = ((B :: Bs).map primeSupportProduct).foldl Nat.gcd
              (primeSupportProduct F0) := rfl

end Omega.Zeta
