import Mathlib.Tactic

namespace Omega.POM

abbrev pom_zero_variance_iff_closure_fiber : Type :=
  Fin 2

noncomputable def pom_zero_variance_iff_closure_trace
    (h : pom_zero_variance_iff_closure_fiber → ℚ) : ℚ :=
  (h 0 + h 1) / 2

def pom_zero_variance_iff_closure_variance
    (h : pom_zero_variance_iff_closure_fiber → ℚ) : ℚ :=
  (h 0 - h 1) ^ 2

def pom_zero_variance_iff_closure_base_field_observable
    (h : pom_zero_variance_iff_closure_fiber → ℚ) : Prop :=
  ∃ c : ℚ, ∀ i, h i = c

def pom_zero_variance_iff_closure_closed_observable
    (h : pom_zero_variance_iff_closure_fiber → ℚ) : Prop :=
  pom_zero_variance_iff_closure_base_field_observable h

def pom_zero_variance_iff_closure_statement : Prop :=
  ∀ h : pom_zero_variance_iff_closure_fiber → ℚ,
    pom_zero_variance_iff_closure_variance h = 0 ↔
      pom_zero_variance_iff_closure_closed_observable h

/-- Paper label: `prop:pom-zero-variance-iff-closure`. -/
theorem paper_pom_zero_variance_iff_closure :
    pom_zero_variance_iff_closure_statement := by
  intro h
  constructor
  · intro hvar
    unfold pom_zero_variance_iff_closure_variance at hvar
    have hdiff : h 0 - h 1 = 0 := sq_eq_zero_iff.mp hvar
    refine ⟨h 0, ?_⟩
    intro i
    fin_cases i
    · rfl
    · exact (sub_eq_zero.mp hdiff).symm
  · rintro ⟨c, hc⟩
    unfold pom_zero_variance_iff_closure_variance
    rw [hc 0, hc 1]
    ring

end Omega.POM
