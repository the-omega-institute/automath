import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part75-triple-frobenius-boolean-independence`. Filtering the
finite product by three independent membership predicates gives the product of the three finite
cardinalities, and normalization by the stated ambient group sizes gives the product density. -/
theorem paper_xi_time_part75_triple_frobenius_boolean_independence {G10 GLY G4 : Type*}
    [Fintype G10] [Fintype GLY] [Fintype G4] [DecidableEq G10] [DecidableEq GLY]
    [DecidableEq G4] (Omega10 : Finset G10) (OmegaLY : Finset GLY) (Omega4 : Finset G4)
    (h10 : Fintype.card G10 = 3628800) (hLY : Fintype.card GLY = 6)
    (h4 : Fintype.card G4 = 48) :
    (((Finset.univ.filter (fun g : G10 × (GLY × G4) =>
          g.1 ∈ Omega10 ∧ g.2.1 ∈ OmegaLY ∧ g.2.2 ∈ Omega4)).card : ℚ) /
        (Fintype.card (G10 × (GLY × G4)) : ℚ)) =
      ((Omega10.card : ℚ) / 3628800) * ((OmegaLY.card : ℚ) / 6) *
        ((Omega4.card : ℚ) / 48) := by
  classical
  have hfilter :
      (Finset.univ.filter (fun g : G10 × (GLY × G4) =>
          g.1 ∈ Omega10 ∧ g.2.1 ∈ OmegaLY ∧ g.2.2 ∈ Omega4)) =
        Omega10.product (OmegaLY.product Omega4) := by
    ext g
    simp
  have hcard :
      (Finset.univ.filter (fun g : G10 × (GLY × G4) =>
          g.1 ∈ Omega10 ∧ g.2.1 ∈ OmegaLY ∧ g.2.2 ∈ Omega4)).card =
        Omega10.card * OmegaLY.card * Omega4.card := by
    simp [hfilter, Finset.card_product, Nat.mul_assoc]
  rw [hcard]
  rw [Fintype.card_prod, Fintype.card_prod, h10, hLY, h4]
  norm_num
  ring_nf

end Omega.Zeta
