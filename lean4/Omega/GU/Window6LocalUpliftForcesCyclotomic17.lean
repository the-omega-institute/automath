import Omega.GU.M11Z34CyclotomicRepresentationRigidity
import Omega.GU.TerminalWindow6LocalUpliftAdmissibility

namespace Omega.GU

/-- Paper-facing wrapper combining the window-6 local uplift certificate with the `m = 11`,
`\QQ[\ZZ_{34}]` cyclotomic decomposition and its intrinsic `C16` Galois action.
    cor:window6-local-uplift-forces-cyclotomic17 -/
theorem paper_window6_local_uplift_forces_cyclotomic17
    (crtDecomposition zeta34EqZeta17 cyclotomicDegree16 galoisGroupC16
      rationalLayerCarriesC16 : Prop)
    (hCRT : crtDecomposition)
    (hZeta : zeta34EqZeta17)
    (hDegree : cyclotomicDegree16)
    (hGalois : Nat.totient 17 = 16 → galoisGroupC16)
    (hAction : galoisGroupC16 → rationalLayerCarriesC16) :
    terminalWindow6LocalUpliftSet = ({0, 34, -34} : Finset ℤ) ∧
      crtDecomposition ∧
      zeta34EqZeta17 ∧
      cyclotomicDegree16 ∧
      Nat.totient 17 = 16 ∧
      galoisGroupC16 ∧
      rationalLayerCarriesC16 := by
  have hCyclotomic :
      crtDecomposition ∧ zeta34EqZeta17 ∧ cyclotomicDegree16 :=
    paper_m11_qz34_cyclotomic_decomposition crtDecomposition zeta34EqZeta17
      cyclotomicDegree16 hCRT hZeta hDegree
  have hC16 :
      Nat.totient 17 = 16 ∧ galoisGroupC16 ∧ rationalLayerCarriesC16 :=
    paper_m11_qz34_galois_c16 galoisGroupC16 rationalLayerCarriesC16 hGalois hAction
  rcases hCyclotomic with ⟨hCRT', hZeta', hDegree'⟩
  rcases hC16 with ⟨hTotient, hGalois', hAction'⟩
  exact ⟨paper_terminal_window6_local_uplift_admissibility, hCRT', hZeta', hDegree', hTotient,
    hGalois', hAction'⟩

end Omega.GU
