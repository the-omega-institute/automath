import Omega.POM.ThreeGenInterfaceNormalForm

namespace Omega.POM

/-- Paper label: `prop:pom-mom-interface-normal-form`. Once a normalizer produces a MOM-interface
normal form for every word, existence is immediate. -/
theorem paper_pom_mom_interface_normal_form {α : Type*} (rewritesTo : α → α → Prop)
    (isMomInterfaceNormalForm : α → Prop) (NF : α → α)
    (hNF : ∀ w, rewritesTo (NF w) w ∧ isMomInterfaceNormalForm (NF w))
    (hCanonical : ∀ w w', rewritesTo w' w → isMomInterfaceNormalForm w' → w' = NF w) :
    ∀ w, ∃ w', rewritesTo w' w ∧ isMomInterfaceNormalForm w' := by
  let _ := hCanonical
  intro w
  exact ⟨NF w, hNF w⟩

end Omega.POM
