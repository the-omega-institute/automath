import Mathlib.Data.Int.NatAbs
import Omega.SPG.CoarsegrainedCutFlux

namespace Omega.SPG

/-- Paper label: `cor:fold-hypercube-boundary-l1-bias-monotone`. -/
theorem paper_fold_hypercube_boundary_l1_bias_monotone {n : ℕ} (i : Fin n)
    (S : Finset (Fin n → Bool)) :
    let pos := (Finset.univ.filter
      (fun ω : Fin n → Bool => ω i = false ∧ ω ∈ S ∧ flipAt i ω ∉ S)).card
    let neg := (Finset.univ.filter
      (fun ω : Fin n → Bool => ω i = false ∧ ω ∉ S ∧ flipAt i ω ∈ S)).card
    Int.natAbs (volumeBias i S) ≤ pos + neg ∧
      (Int.natAbs (volumeBias i S) = pos + neg ↔ pos = 0 ∨ neg = 0) := by
  dsimp
  rw [← cutFlux_eq_volumeBias]
  by_cases hneg : (Finset.univ.filter
      (fun ω : Fin n → Bool => ω i = false ∧ ω ∉ S ∧ flipAt i ω ∈ S)).card ≤
    (Finset.univ.filter
      (fun ω : Fin n → Bool => ω i = false ∧ ω ∈ S ∧ flipAt i ω ∉ S)).card
  · have hnatAbs :
        Int.natAbs
            (((Finset.univ.filter
                (fun ω : Fin n → Bool => ω i = false ∧ ω ∈ S ∧ flipAt i ω ∉ S)).card : ℤ) -
              (Finset.univ.filter
                (fun ω : Fin n → Bool => ω i = false ∧ ω ∉ S ∧ flipAt i ω ∈ S)).card) =
          (Finset.univ.filter
            (fun ω : Fin n → Bool => ω i = false ∧ ω ∈ S ∧ flipAt i ω ∉ S)).card -
            (Finset.univ.filter
              (fun ω : Fin n → Bool => ω i = false ∧ ω ∉ S ∧ flipAt i ω ∈ S)).card := by
      simpa using Int.natAbs_natCast_sub_natCast_of_ge hneg
    constructor
    · rw [cutFlux, hnatAbs]
      omega
    · rw [cutFlux, hnatAbs]
      omega
  · have hpos :
        (Finset.univ.filter
            (fun ω : Fin n → Bool => ω i = false ∧ ω ∈ S ∧ flipAt i ω ∉ S)).card ≤
          (Finset.univ.filter
            (fun ω : Fin n → Bool => ω i = false ∧ ω ∉ S ∧ flipAt i ω ∈ S)).card := by
      omega
    have hnatAbs :
        Int.natAbs
            (((Finset.univ.filter
                (fun ω : Fin n → Bool => ω i = false ∧ ω ∈ S ∧ flipAt i ω ∉ S)).card : ℤ) -
              (Finset.univ.filter
                (fun ω : Fin n → Bool => ω i = false ∧ ω ∉ S ∧ flipAt i ω ∈ S)).card) =
          (Finset.univ.filter
            (fun ω : Fin n → Bool => ω i = false ∧ ω ∉ S ∧ flipAt i ω ∈ S)).card -
            (Finset.univ.filter
              (fun ω : Fin n → Bool => ω i = false ∧ ω ∈ S ∧ flipAt i ω ∉ S)).card := by
      simpa using Int.natAbs_natCast_sub_natCast_of_le hpos
    constructor
    · rw [cutFlux, hnatAbs]
      omega
    · rw [cutFlux, hnatAbs]
      omega

end Omega.SPG
