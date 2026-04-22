import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic

namespace Omega.Zeta

/-- The external audit factor `S₁₀ × (S₄ × C₂)` from the part-62eb density computation. -/
abbrev xi_time_part62eb_leyang_external_audit_immunity_external_group :=
  Equiv.Perm (Fin 10) × (Equiv.Perm (Fin 4) × Fin 2)

/-- The Lee--Yang splitting factor `S₃`. -/
abbrev xi_time_part62eb_leyang_external_audit_immunity_leyang_group :=
  Equiv.Perm (Fin 3)

/-- External-event density inside `S₁₀ × (S₄ × C₂)`. -/
noncomputable def xi_time_part62eb_leyang_external_audit_immunity_external_density
    (E : Finset xi_time_part62eb_leyang_external_audit_immunity_external_group) : ℚ :=
  (E.card : ℚ) / Fintype.card xi_time_part62eb_leyang_external_audit_immunity_external_group

/-- Conditional Lee--Yang density obtained by factoring the joint density over the direct product
`(S₁₀ × (S₄ × C₂)) × S₃` and dividing by the external-event density. -/
noncomputable def xi_time_part62eb_leyang_external_audit_immunity_conditional_density
    (E : Finset xi_time_part62eb_leyang_external_audit_immunity_external_group)
    (D : Finset xi_time_part62eb_leyang_external_audit_immunity_leyang_group) : ℚ :=
  (xi_time_part62eb_leyang_external_audit_immunity_external_density E *
      ((D.card : ℚ) /
        Fintype.card xi_time_part62eb_leyang_external_audit_immunity_leyang_group)) /
    xi_time_part62eb_leyang_external_audit_immunity_external_density E

/-- Every nonempty external audit event in `S₁₀ × (S₄ × C₂)` leaves the conditional Lee--Yang law
equal to `|D| / 6`. -/
abbrev xi_time_part62eb_leyang_external_audit_immunity_statement : Prop :=
  ∀ (E : Finset xi_time_part62eb_leyang_external_audit_immunity_external_group)
    (D : Finset xi_time_part62eb_leyang_external_audit_immunity_leyang_group),
    E.Nonempty →
      xi_time_part62eb_leyang_external_audit_immunity_conditional_density E D =
        (D.card : ℚ) / 6

/-- Paper label: `prop:xi-time-part62eb-leyang-external-audit-immunity`. -/
theorem paper_xi_time_part62eb_leyang_external_audit_immunity :
    xi_time_part62eb_leyang_external_audit_immunity_statement := by
  intro E D hE
  have hEvent :
      xi_time_part62eb_leyang_external_audit_immunity_external_density E ≠ 0 := by
    unfold xi_time_part62eb_leyang_external_audit_immunity_external_density
    refine div_ne_zero ?_ ?_
    · exact_mod_cast Finset.card_ne_zero.mpr hE
    · positivity
  have hCancel :
      xi_time_part62eb_leyang_external_audit_immunity_conditional_density E D =
        (D.card : ℚ) /
          Fintype.card xi_time_part62eb_leyang_external_audit_immunity_leyang_group := by
    unfold xi_time_part62eb_leyang_external_audit_immunity_conditional_density
      xi_time_part62eb_leyang_external_audit_immunity_external_density
    field_simp [hEvent]
  calc
    xi_time_part62eb_leyang_external_audit_immunity_conditional_density E D
      = (D.card : ℚ) /
          Fintype.card xi_time_part62eb_leyang_external_audit_immunity_leyang_group := hCancel
    _ = (D.card : ℚ) / 6 := by norm_num [Fintype.card_perm]

end Omega.Zeta
