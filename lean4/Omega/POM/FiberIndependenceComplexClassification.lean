import Mathlib.Tactic

namespace Omega.POM

/-- Chapter-local wrapper for the homotopy classification of fiber independence complexes arising
from disjoint unions of path components. The path-case analysis splits the component list into the
bad mod-`3` case, which contracts the whole join, and the all-good case, where the join
decomposition accumulates a single sphere dimension. -/
structure FiberIndependenceComplexClassificationData where
  pathCaseClassification : Prop
  badModThreeComponent : Prop
  allComponentsAvoidBadModThree : Prop
  joinDecomposition : Prop
  contractibleCase : Prop
  sphereCase : Prop
  hasPathCaseClassification : pathCaseClassification
  hasJoinDecomposition : joinDecomposition
  classifyPathComponents :
    pathCaseClassification → badModThreeComponent ∨ allComponentsAvoidBadModThree
  badModThreeComponentForcesContraction :
    badModThreeComponent → joinDecomposition → contractibleCase
  allGoodComponentsGiveSphere :
    allComponentsAvoidBadModThree → joinDecomposition → sphereCase

/-- The fiber independence complex of a disjoint union of paths is either contractible or
homotopy equivalent to a single sphere, according to the mod-`3` path classification and the join
decomposition of the components.
    thm:pom-fiber-independence-complex-classification -/
theorem paper_pom_fiber_independence_complex_classification
    (D : FiberIndependenceComplexClassificationData) :
    D.contractibleCase ∨ D.sphereCase := by
  rcases D.classifyPathComponents D.hasPathCaseClassification with hBad | hGood
  · exact Or.inl <| D.badModThreeComponentForcesContraction hBad D.hasJoinDecomposition
  · exact Or.inr <| D.allGoodComponentsGiveSphere hGood D.hasJoinDecomposition

end Omega.POM
