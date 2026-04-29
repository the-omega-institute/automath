import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete data for the coordinate-bundle atomic integrability/logscale interface. -/
structure conclusion_coordinatebundle_atomic_integrability_logscale_Data where
  conclusion_coordinatebundle_atomic_integrability_logscale_m : ℕ
  conclusion_coordinatebundle_atomic_integrability_logscale_n : ℕ
  conclusion_coordinatebundle_atomic_integrability_logscale_s : ℕ
  conclusion_coordinatebundle_atomic_integrability_logscale_LJ : ℕ
  conclusion_coordinatebundle_atomic_integrability_logscale_Delta : ℕ
  conclusion_coordinatebundle_atomic_integrability_logscale_shannon : ℕ
  conclusion_coordinatebundle_atomic_integrability_logscale_audit : ℕ
  conclusion_coordinatebundle_atomic_integrability_logscale_linear : ℕ
  conclusion_coordinatebundle_atomic_integrability_logscale_kolmogorov : ℕ
  conclusion_coordinatebundle_atomic_integrability_logscale_Cm : ℕ
  conclusion_coordinatebundle_atomic_integrability_logscale_CmDrop : ℕ
  conclusion_coordinatebundle_atomic_integrability_logscale_LJ_eq :
    conclusion_coordinatebundle_atomic_integrability_logscale_LJ =
      2 ^
        (conclusion_coordinatebundle_atomic_integrability_logscale_m *
          (conclusion_coordinatebundle_atomic_integrability_logscale_n -
            conclusion_coordinatebundle_atomic_integrability_logscale_s))
  conclusion_coordinatebundle_atomic_integrability_logscale_Delta_eq :
    conclusion_coordinatebundle_atomic_integrability_logscale_Delta =
      conclusion_coordinatebundle_atomic_integrability_logscale_LJ
  conclusion_coordinatebundle_atomic_integrability_logscale_shannon_eq :
    conclusion_coordinatebundle_atomic_integrability_logscale_shannon =
      conclusion_coordinatebundle_atomic_integrability_logscale_Delta
  conclusion_coordinatebundle_atomic_integrability_logscale_audit_eq :
    conclusion_coordinatebundle_atomic_integrability_logscale_audit =
      conclusion_coordinatebundle_atomic_integrability_logscale_Delta
  conclusion_coordinatebundle_atomic_integrability_logscale_linear_eq :
    conclusion_coordinatebundle_atomic_integrability_logscale_linear =
      conclusion_coordinatebundle_atomic_integrability_logscale_Delta
  conclusion_coordinatebundle_atomic_integrability_logscale_kolmogorov_eq :
    conclusion_coordinatebundle_atomic_integrability_logscale_kolmogorov =
      conclusion_coordinatebundle_atomic_integrability_logscale_Delta
  conclusion_coordinatebundle_atomic_integrability_logscale_Cm_drop_law :
    conclusion_coordinatebundle_atomic_integrability_logscale_Cm =
      conclusion_coordinatebundle_atomic_integrability_logscale_CmDrop +
        conclusion_coordinatebundle_atomic_integrability_logscale_m *
          (conclusion_coordinatebundle_atomic_integrability_logscale_n -
            conclusion_coordinatebundle_atomic_integrability_logscale_s)

/-- Locked equalities for the atomic coordinate bundle and its affine log-scale drop law. -/
def conclusion_coordinatebundle_atomic_integrability_logscale_statement
    (D : conclusion_coordinatebundle_atomic_integrability_logscale_Data) : Prop :=
  D.conclusion_coordinatebundle_atomic_integrability_logscale_Delta =
      2 ^
        (D.conclusion_coordinatebundle_atomic_integrability_logscale_m *
          (D.conclusion_coordinatebundle_atomic_integrability_logscale_n -
            D.conclusion_coordinatebundle_atomic_integrability_logscale_s)) ∧
    D.conclusion_coordinatebundle_atomic_integrability_logscale_shannon =
      2 ^
        (D.conclusion_coordinatebundle_atomic_integrability_logscale_m *
          (D.conclusion_coordinatebundle_atomic_integrability_logscale_n -
            D.conclusion_coordinatebundle_atomic_integrability_logscale_s)) ∧
    D.conclusion_coordinatebundle_atomic_integrability_logscale_audit =
      2 ^
        (D.conclusion_coordinatebundle_atomic_integrability_logscale_m *
          (D.conclusion_coordinatebundle_atomic_integrability_logscale_n -
            D.conclusion_coordinatebundle_atomic_integrability_logscale_s)) ∧
    D.conclusion_coordinatebundle_atomic_integrability_logscale_linear =
      2 ^
        (D.conclusion_coordinatebundle_atomic_integrability_logscale_m *
          (D.conclusion_coordinatebundle_atomic_integrability_logscale_n -
            D.conclusion_coordinatebundle_atomic_integrability_logscale_s)) ∧
    D.conclusion_coordinatebundle_atomic_integrability_logscale_kolmogorov =
      2 ^
        (D.conclusion_coordinatebundle_atomic_integrability_logscale_m *
          (D.conclusion_coordinatebundle_atomic_integrability_logscale_n -
            D.conclusion_coordinatebundle_atomic_integrability_logscale_s)) ∧
    D.conclusion_coordinatebundle_atomic_integrability_logscale_Cm =
      D.conclusion_coordinatebundle_atomic_integrability_logscale_CmDrop +
        D.conclusion_coordinatebundle_atomic_integrability_logscale_m *
          (D.conclusion_coordinatebundle_atomic_integrability_logscale_n -
            D.conclusion_coordinatebundle_atomic_integrability_logscale_s)

/-- Paper label: `thm:conclusion-coordinatebundle-atomic-integrability-logscale`. -/
theorem paper_conclusion_coordinatebundle_atomic_integrability_logscale
    (D : conclusion_coordinatebundle_atomic_integrability_logscale_Data) :
    conclusion_coordinatebundle_atomic_integrability_logscale_statement D := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [D.conclusion_coordinatebundle_atomic_integrability_logscale_Delta_eq,
      D.conclusion_coordinatebundle_atomic_integrability_logscale_LJ_eq]
  · rw [D.conclusion_coordinatebundle_atomic_integrability_logscale_shannon_eq,
      D.conclusion_coordinatebundle_atomic_integrability_logscale_Delta_eq,
      D.conclusion_coordinatebundle_atomic_integrability_logscale_LJ_eq]
  · rw [D.conclusion_coordinatebundle_atomic_integrability_logscale_audit_eq,
      D.conclusion_coordinatebundle_atomic_integrability_logscale_Delta_eq,
      D.conclusion_coordinatebundle_atomic_integrability_logscale_LJ_eq]
  · rw [D.conclusion_coordinatebundle_atomic_integrability_logscale_linear_eq,
      D.conclusion_coordinatebundle_atomic_integrability_logscale_Delta_eq,
      D.conclusion_coordinatebundle_atomic_integrability_logscale_LJ_eq]
  · rw [D.conclusion_coordinatebundle_atomic_integrability_logscale_kolmogorov_eq,
      D.conclusion_coordinatebundle_atomic_integrability_logscale_Delta_eq,
      D.conclusion_coordinatebundle_atomic_integrability_logscale_LJ_eq]
  · exact D.conclusion_coordinatebundle_atomic_integrability_logscale_Cm_drop_law

end Omega.Conclusion
