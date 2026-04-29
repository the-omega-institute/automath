import Mathlib.Tactic

namespace Omega.POM

/-- The comparison relation on the bounded three-generator slice: two words agree exactly when
their normal forms and anomaly certificates agree. -/
def pom_three_gen_normal_form_decidable_relation {α τ υ : Type*}
    (NF : α → τ) (Anom : α → υ) (x y : α) : Prop :=
  NF x = NF y ∧ Anom x = Anom y

/-- Decidability of the normal-form-plus-anomaly comparison on the bounded slice. -/
def pom_three_gen_normal_form_decidable_statement {α τ υ : Type*}
    (NF : α → τ) (Anom : α → υ) : Prop :=
  Nonempty (∀ x y : α, Decidable (pom_three_gen_normal_form_decidable_relation NF Anom x y))

/-- Paper label: `cor:pom-three-gen-normal-form-decidable`. Once the comparison on the bounded
three-generator slice is reduced to equality of the normal form and the finite anomaly data, the
decision procedure is inherited from the ambient `DecidableEq` instances. -/
theorem paper_pom_three_gen_normal_form_decidable {α τ υ : Type*} [DecidableEq τ] [DecidableEq υ]
    (NF : α → τ) (Anom : α → υ) : pom_three_gen_normal_form_decidable_statement NF Anom := by
  refine ⟨?_⟩
  intro x y
  simpa [pom_three_gen_normal_form_decidable_relation] using
    (inferInstance : Decidable (NF x = NF y ∧ Anom x = Anom y))

end Omega.POM
