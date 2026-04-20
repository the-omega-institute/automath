import Omega.Zeta.CyclicEulerProductComplexSection

namespace Omega.Discussion

/-- Discussion-level wrapper around the cyclic Euler-product complex-section theorem.
    thm:discussion-traceclass-fredholm-euler-surjection -/
theorem paper_discussion_traceclass_fredholm_euler_surjection {α r : ℤ}
    (D : Omega.Zeta.CyclicEulerProductComplexSectionData α r) :
    D.traceClassWitness → D.directSumRealization → D.complexSection := by
  exact Omega.Zeta.paper_cyclic_euler_product_complex_section D

end Omega.Discussion
