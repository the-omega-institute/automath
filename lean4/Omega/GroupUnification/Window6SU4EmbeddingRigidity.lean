import Mathlib.Tactic
import Omega.GroupUnification.Window6CommonRefinementSMLevi

namespace Omega.GroupUnification

/-- Corollary wrapper: once the orbit dictionary pins down the standard
`su(3) ⊕ u(1) ⊂ su(4)` embedding, the existing conjugacy uniqueness layer
promotes it to full embedding rigidity. `cor:window6-su4-embedding-rigidity` -/
theorem paper_window6_su4_embedding_rigidity
    (orbit_dictionary_compatible standard_embedding all_embeddings_conjugate : Prop)
    (hStandard : orbit_dictionary_compatible → standard_embedding)
    (hConjugate : standard_embedding → all_embeddings_conjugate) :
    orbit_dictionary_compatible → standard_embedding ∧ all_embeddings_conjugate := by
  intro horbit
  constructor
  · exact hStandard horbit
  · exact hConjugate (hStandard horbit)

end Omega.GroupUnification
