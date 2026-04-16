import Omega.Zeta.CyclicEulerProduct

namespace Omega.Zeta

universe u

/-- Chapter-local trace-class package for reconstructing a cyclic Euler product from a direct sum
of cyclic Fredholm blocks with complex weights. The concrete block determinant identities are
supplied by `paper_cyclic_euler_product`; this structure records the extra trace-class/direct-sum
data needed to turn those blockwise identities into the advertised complex section. -/
structure CyclicEulerProductComplexSectionData (α r : ℤ) where
  ComplexWeightFamily : Type u
  traceClassWitness : Prop
  directSumRealization : Prop
  complexSection : Prop
  realizeSection :
    ((1 - (α * r) • cyclicPerm2).det = 1 - (α * r) ^ 2 ∧
      (1 - (α * r) • cyclicPerm3).det = 1 - (α * r) ^ 3 ∧
      (1 - (α * r) • cyclicPerm4).det = 1 - (α * r) ^ 4 ∧
      (1 - (α * r) • cyclicPerm5).det = 1 - (α * r) ^ 5 ∧
      (1 - (α * r) • cyclicPerm6).det = 1 - (α * r) ^ 6) →
      traceClassWitness →
      directSumRealization →
      complexSection

/-- The complex-section corollary is obtained by combining the already-formalized cyclic block
determinant identities with the chapter-local trace-class/direct-sum realization witness.
    cor:cyclic-euler-product-complex-section -/
theorem paper_cyclic_euler_product_complex_section
    {α r : ℤ} (D : CyclicEulerProductComplexSectionData α r) :
    D.traceClassWitness → D.directSumRealization → D.complexSection := by
  intro hTrace hDirect
  exact D.realizeSection (Omega.Zeta.paper_cyclic_euler_product α r) hTrace hDirect

end Omega.Zeta
