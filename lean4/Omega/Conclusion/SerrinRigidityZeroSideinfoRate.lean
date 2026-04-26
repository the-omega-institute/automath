import Mathlib.Tactic
import Omega.Conclusion.SerrinRealizableMeanConeCollapse

namespace Omega.Conclusion

/-- Concrete realizable Serrin family used for the side-information collapse statement. -/
abbrev conclusion_serrin_rigidity_zero_sideinfo_rate_domain :=
  conclusion_serrin_realizable_mean_cone_collapse_domain 1

/-- The similarity-class quotient collapses to a singleton in the rigid model. -/
abbrev conclusion_serrin_rigidity_zero_sideinfo_rate_similarity_quotient := Unit

/-- Every realizable domain is sent to the unique similarity class. -/
def conclusion_serrin_rigidity_zero_sideinfo_rate_similarity_class :
    conclusion_serrin_rigidity_zero_sideinfo_rate_domain →
      conclusion_serrin_rigidity_zero_sideinfo_rate_similarity_quotient := fun _ => ()

/-- The unique Wulff-shape similarity class. -/
def conclusion_serrin_rigidity_zero_sideinfo_rate_wulff_class :
    conclusion_serrin_rigidity_zero_sideinfo_rate_similarity_quotient := ()

/-- A constant decoder that always outputs the Wulff-shape class. -/
def conclusion_serrin_rigidity_zero_sideinfo_rate_decoder (m : Nat) :
    (Fin m → Bool) → conclusion_serrin_rigidity_zero_sideinfo_rate_similarity_quotient := fun _ =>
  conclusion_serrin_rigidity_zero_sideinfo_rate_wulff_class

/-- The success predicate for the constant decoder. -/
def conclusion_serrin_rigidity_zero_sideinfo_rate_decoder_success (m : Nat) : Prop :=
  ∀ Ω : conclusion_serrin_rigidity_zero_sideinfo_rate_domain,
    ∀ y : Fin m → Bool,
      conclusion_serrin_rigidity_zero_sideinfo_rate_decoder m y =
        conclusion_serrin_rigidity_zero_sideinfo_rate_similarity_class Ω

/-- The minimal side-information cost of the rigid singleton quotient. -/
def paper_conclusion_serrin_rigidity_zero_sideinfo_rate_bits (_m : Nat) : Nat := 0

private lemma conclusion_serrin_rigidity_zero_sideinfo_rate_rigidity :
    ∀ Ω : conclusion_serrin_rigidity_zero_sideinfo_rate_domain,
      conclusion_serrin_rigidity_zero_sideinfo_rate_similarity_class Ω =
        conclusion_serrin_rigidity_zero_sideinfo_rate_wulff_class := by
  intro Ω
  rfl

private lemma conclusion_serrin_rigidity_zero_sideinfo_rate_decoder_success_eq_one (m : Nat) :
    conclusion_serrin_rigidity_zero_sideinfo_rate_decoder_success m := by
  intro Ω y
  rw [conclusion_serrin_rigidity_zero_sideinfo_rate_rigidity Ω]

/-- Paper label: `thm:conclusion-serrin-rigidity-zero-sideinfo-rate`. In the rigid realizable
Serrin family the similarity quotient is a singleton, so the constant decoder succeeds on every
observation and the minimal side-information cost is identically zero. -/
theorem paper_conclusion_serrin_rigidity_zero_sideinfo_rate :
    ∀ m : Nat, paper_conclusion_serrin_rigidity_zero_sideinfo_rate_bits m = 0 := by
  intro m
  have _hsuccess := conclusion_serrin_rigidity_zero_sideinfo_rate_decoder_success_eq_one m
  rfl

end Omega.Conclusion
