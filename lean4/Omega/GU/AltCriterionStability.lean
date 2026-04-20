import Mathlib.Tactic
import Omega.GU.DiscriminantSquareclass

namespace Omega.GU

variable {K : Type*} [Field K]

/-- For quadratics, both the original and transported discriminants are explicit squares, so the
alternative square criterion is stable under the Joukowsky--Godel transport.
    cor:group-jg-alt-criterion-stability -/
theorem paper_group_jg_alt_criterion_stability
    (a_n a_0 r z₁ z₂ : K) (hr : r ≠ 0) (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0)
    (hVieta : a_n * (z₁ * z₂) = a_0) :
    let D := Omega.GU.quadraticJoukowskyGodelTransportData a_n a_0 r z₁ z₂ hVieta
    let ΔQ := Omega.GU.quadraticPolynomialDiscriminant D.transportLeadingCoeff
      (Omega.GU.quadraticTransportRoot r z₁) (Omega.GU.quadraticTransportRoot r z₂)
    let ΔP := Omega.GU.quadraticPolynomialDiscriminant a_n z₁ z₂
    (∃ x : K, ΔP = x ^ 2) ↔ ∃ y : K, ΔQ = y ^ 2 := by
  let _ := hr
  let _ := hz₁
  let _ := hz₂
  dsimp [quadraticPolynomialDiscriminant]
  constructor <;> intro _
  · refine ⟨(quadraticJoukowskyGodelTransportData a_n a_0 r z₁ z₂ hVieta).transportLeadingCoeff *
      (quadraticTransportRoot r z₁ - quadraticTransportRoot r z₂), by ring⟩
  · refine ⟨a_n * (z₁ - z₂), by ring⟩

end Omega.GU
