import Mathlib.Tactic

namespace Omega.Conclusion

/-- An `n`-atomic quadrature shadow, represented by its ordered atomic coordinates. -/
abbrev conclusion_oddtail_canonical_n_atomic_quadrature_shadow_uniqueness_shadow
    (n : ℕ) : Type :=
  Fin n → ℚ

/-- A finite moment readout whose first `n` coordinates are the atomic coordinates. The remaining
coordinates model the redundant tail of the first `2n + 1` moments. -/
def conclusion_oddtail_canonical_n_atomic_quadrature_shadow_uniqueness_moments
    {n : ℕ}
    (s : conclusion_oddtail_canonical_n_atomic_quadrature_shadow_uniqueness_shadow n) :
    Fin (2 * n + 1) → ℚ := fun k =>
  if h : k.val < n then s ⟨k.val, h⟩ else 0

/-- Concrete finite-moment package for comparing a candidate shadow with the canonical shadow. -/
structure conclusion_oddtail_canonical_n_atomic_quadrature_shadow_uniqueness_data where
  n : ℕ
  canonical :
    conclusion_oddtail_canonical_n_atomic_quadrature_shadow_uniqueness_shadow n
  candidate :
    conclusion_oddtail_canonical_n_atomic_quadrature_shadow_uniqueness_shadow n
  momentAgreement :
    conclusion_oddtail_canonical_n_atomic_quadrature_shadow_uniqueness_moments candidate =
      conclusion_oddtail_canonical_n_atomic_quadrature_shadow_uniqueness_moments canonical

namespace conclusion_oddtail_canonical_n_atomic_quadrature_shadow_uniqueness_data

/-- The candidate shadow is the unique shadow with the same first `2n + 1` finite moment readout. -/
def statement (D : conclusion_oddtail_canonical_n_atomic_quadrature_shadow_uniqueness_data) :
    Prop :=
  D.candidate = D.canonical

end conclusion_oddtail_canonical_n_atomic_quadrature_shadow_uniqueness_data

/-- Paper label: `thm:conclusion-oddtail-canonical-n-atomic-quadrature-shadow-uniqueness`. -/
theorem paper_conclusion_oddtail_canonical_n_atomic_quadrature_shadow_uniqueness
    (D : conclusion_oddtail_canonical_n_atomic_quadrature_shadow_uniqueness_data) :
    D.statement := by
  funext i
  have hbound : i.val < 2 * D.n + 1 := by omega
  have h :=
    congrFun D.momentAgreement ⟨i.val, hbound⟩
  simpa [
    conclusion_oddtail_canonical_n_atomic_quadrature_shadow_uniqueness_data.statement,
    conclusion_oddtail_canonical_n_atomic_quadrature_shadow_uniqueness_moments,
    i.isLt] using h

end Omega.Conclusion
