import Omega.Zeta.XiSliceHorizonCarathToeplitz

namespace Omega.Zeta

/-- Paper label: `cor:xi-slice-weyl-herglotz`. -/
theorem paper_xi_slice_weyl_herglotz
    (xiZerosOnCriticalLine phiRootsOnCircle caratheodoryPositive toeplitzPsd
      herglotzPositive : Prop)
    (h12 : xiZerosOnCriticalLine ↔ phiRootsOnCircle)
    (h23 : phiRootsOnCircle ↔ caratheodoryPositive)
    (h34 : caratheodoryPositive ↔ toeplitzPsd)
    (h15 : xiZerosOnCriticalLine ↔ herglotzPositive) :
    (xiZerosOnCriticalLine ↔ phiRootsOnCircle) ∧
      (xiZerosOnCriticalLine ↔ caratheodoryPositive) ∧
        (xiZerosOnCriticalLine ↔ toeplitzPsd) ∧
          (xiZerosOnCriticalLine ↔ herglotzPositive) := by
  exact ⟨h12, h12.trans h23, (h12.trans h23).trans h34, h15⟩

end Omega.Zeta
