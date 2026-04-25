import Omega.POM.ThreeGenTermination

namespace Omega.POM

/-- Paper label: `prop:pom-three-gen-interface-normal-form`. -/
theorem paper_pom_three_gen_interface_normal_form
    (rewritesTo : pom_three_gen_termination_word -> pom_three_gen_termination_word -> Prop)
    (isInterfaceNormalForm : pom_three_gen_termination_word -> Prop)
    (NF : pom_three_gen_termination_word -> pom_three_gen_termination_word)
    (hNF : forall w, rewritesTo (NF w) w /\ isInterfaceNormalForm (NF w))
    (hCanonical : forall w w', rewritesTo w' w -> isInterfaceNormalForm w' -> w' = NF w) :
    forall w, exists w', rewritesTo w' w /\ isInterfaceNormalForm w' := by
  let _ := hCanonical
  intro w
  refine ⟨NF w, ?_⟩
  exact hNF w

end Omega.POM
