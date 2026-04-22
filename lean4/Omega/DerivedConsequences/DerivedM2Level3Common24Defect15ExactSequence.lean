import Mathlib.Tactic

namespace Omega.DerivedConsequences

/-- The shared `ℚ ⊕ V24` side, modeled as one distinguished scalar slot together with `24`
visible coordinates. -/
abbrev derived_m2_level3_common24_defect15_exact_sequence_shared := Fin 1 ⊕ Fin 24

/-- The visible `24`-dimensional summand. -/
abbrev derived_m2_level3_common24_defect15_exact_sequence_visible := Fin 24

/-- The hidden defect-`15` summand. -/
abbrev derived_m2_level3_common24_defect15_exact_sequence_defect := Fin 15

/-- Distinguished basepoint representing the common scalar summand. -/
def derived_m2_level3_common24_defect15_exact_sequence_basepoint :
    derived_m2_level3_common24_defect15_exact_sequence_shared :=
  Sum.inl 0

/-- Inclusion of the visible `24`-dimensional summand. -/
def derived_m2_level3_common24_defect15_exact_sequence_visible_inclusion :
    derived_m2_level3_common24_defect15_exact_sequence_visible →
      derived_m2_level3_common24_defect15_exact_sequence_shared :=
  Sum.inr

/-- The finite-rank decomposed object carrying the common part together with the `15`-dimensional
defect summand. -/
abbrev derived_m2_level3_common24_defect15_exact_sequence_ambient :=
  derived_m2_level3_common24_defect15_exact_sequence_shared ×
    derived_m2_level3_common24_defect15_exact_sequence_defect

/-- Inclusion of the defect summand as the kernel over the shared basepoint. -/
def derived_m2_level3_common24_defect15_exact_sequence_inclusion :
    derived_m2_level3_common24_defect15_exact_sequence_defect →
      derived_m2_level3_common24_defect15_exact_sequence_ambient :=
  fun d => (derived_m2_level3_common24_defect15_exact_sequence_basepoint, d)

/-- Projection to the shared `ℚ ⊕ V24` summand. -/
def derived_m2_level3_common24_defect15_exact_sequence_projection :
    derived_m2_level3_common24_defect15_exact_sequence_ambient →
      derived_m2_level3_common24_defect15_exact_sequence_shared :=
  Prod.fst

/-- Concrete exact-sequence package with explicit kernel, image, cokernel, and visible-rank
counts. -/
def derived_m2_level3_common24_defect15_exact_sequence_statement : Prop :=
  (∀ d,
    derived_m2_level3_common24_defect15_exact_sequence_projection
        (derived_m2_level3_common24_defect15_exact_sequence_inclusion d) =
      derived_m2_level3_common24_defect15_exact_sequence_basepoint) ∧
    (∀ z : derived_m2_level3_common24_defect15_exact_sequence_ambient,
      derived_m2_level3_common24_defect15_exact_sequence_projection z =
          derived_m2_level3_common24_defect15_exact_sequence_basepoint ↔
        ∃ d,
          derived_m2_level3_common24_defect15_exact_sequence_inclusion d = z) ∧
    Function.Surjective derived_m2_level3_common24_defect15_exact_sequence_projection ∧
    (∀ s : derived_m2_level3_common24_defect15_exact_sequence_shared,
      s = derived_m2_level3_common24_defect15_exact_sequence_basepoint ∨
        ∃ v : derived_m2_level3_common24_defect15_exact_sequence_visible,
          derived_m2_level3_common24_defect15_exact_sequence_visible_inclusion v = s) ∧
    Fintype.card derived_m2_level3_common24_defect15_exact_sequence_visible = 24 ∧
    Fintype.card derived_m2_level3_common24_defect15_exact_sequence_defect = 15

/-- Paper label: `thm:derived-m2-level3-common24-defect15-exact-sequence`. The shared side is the
explicit `ℚ ⊕ V24` sum, the kernel is exactly the `15`-dimensional defect summand, the projection
is surjective, and the visible common part has cardinality `24`. -/
theorem paper_derived_m2_level3_common24_defect15_exact_sequence :
    derived_m2_level3_common24_defect15_exact_sequence_statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro d
    rfl
  · rintro ⟨s, d⟩
    constructor
    · intro hs
      cases hs
      exact ⟨d, rfl⟩
    · rintro ⟨d', hd'⟩
      cases hd'
      rfl
  · intro s
    exact ⟨(s, 0), rfl⟩
  · intro s
    cases s with
    | inl q =>
        left
        have hq : q = 0 := Fin.eq_zero q
        cases hq
        rfl
    | inr v =>
        right
        exact ⟨v, rfl⟩
  · simp
  · simp

end Omega.DerivedConsequences
