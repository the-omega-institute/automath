import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-fiber-isomorphic-homotopy-rigidity`. -/
theorem paper_conclusion_fiber_isomorphic_homotopy_rigidity {K : Type*}
    (HomotopyEquiv : K → K → Prop) (Noncontractible : K → Prop) (Kx Ky : K)
    (tauX tauY dX dY : ℕ) (hHom : HomotopyEquiv Kx Ky)
    (hNoncontractible : Noncontractible Kx ↔ Noncontractible Ky)
    (hTau : Noncontractible Kx → tauX = tauY)
    (hParityX : Noncontractible Kx ↔ dX % 2 = 1)
    (hParityY : Noncontractible Ky ↔ dY % 2 = 1) :
    HomotopyEquiv Kx Ky ∧ (Noncontractible Kx ↔ Noncontractible Ky) ∧
      (Noncontractible Kx → tauX = tauY) ∧ dX % 2 = dY % 2 := by
  refine ⟨hHom, hNoncontractible, hTau, ?_⟩
  have hOdd : dX % 2 = 1 ↔ dY % 2 = 1 :=
    hParityX.symm.trans (hNoncontractible.trans hParityY)
  have hXlt : dX % 2 < 2 := Nat.mod_lt dX (by decide)
  have hYlt : dY % 2 < 2 := Nat.mod_lt dY (by decide)
  by_cases hXodd : dX % 2 = 1
  · have hYodd : dY % 2 = 1 := hOdd.mp hXodd
    omega
  · have hYnot : dY % 2 ≠ 1 := fun hYodd => hXodd (hOdd.mpr hYodd)
    omega

end Omega.Conclusion
