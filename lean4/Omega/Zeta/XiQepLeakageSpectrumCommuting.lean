import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Leakage index of a scalar commuting mode, recorded as a logarithmic half-ratio. -/
noncomputable def xi_qep_leakage_spectrum_commuting_leakageIndex (alpha beta : ℝ) :
    ℝ :=
  (Real.log beta - Real.log alpha) / 2

/-- The two critical-line real parts forced by reciprocal pairing. -/
noncomputable def xi_qep_leakage_spectrum_commuting_criticalLines (L lambda : ℝ) :
    Set ℝ :=
  {x | x = (1 / 2 : ℝ) - lambda / Real.log L ∨
    x = (1 / 2 : ℝ) + lambda / Real.log L}

/-- The four real parts in the split-real-root discriminant regime. -/
noncomputable def xi_qep_leakage_spectrum_commuting_splitLines
    (L rPlus rMinus : ℝ) : Set ℝ :=
  {x | x = (1 / 2 : ℝ) + Real.log rPlus / Real.log L ∨
    x = (1 / 2 : ℝ) - Real.log rPlus / Real.log L ∨
    x = (1 / 2 : ℝ) + Real.log rMinus / Real.log L ∨
    x = (1 / 2 : ℝ) - Real.log rMinus / Real.log L}

/-- Modal real-part spectrum obtained by splitting on the scalar discriminant. -/
noncomputable def xi_qep_leakage_spectrum_commuting_modalRealParts
    (L lambda Delta rPlus rMinus : ℝ) : Set ℝ :=
  if Delta ≤ 0 then
    xi_qep_leakage_spectrum_commuting_criticalLines L lambda
  else
    xi_qep_leakage_spectrum_commuting_splitLines L rPlus rMinus

/-- Paper-facing statement for `cor:xi-qep-leakage-spectrum-commuting`. -/
noncomputable def xi_qep_leakage_spectrum_commuting_statement : Prop :=
  ∀ L alpha beta Delta rPlus rMinus : ℝ,
    let lambda := xi_qep_leakage_spectrum_commuting_leakageIndex alpha beta
    (Delta < 0 →
      xi_qep_leakage_spectrum_commuting_modalRealParts L lambda Delta rPlus rMinus =
        xi_qep_leakage_spectrum_commuting_criticalLines L lambda) ∧
    (Delta = 0 →
      xi_qep_leakage_spectrum_commuting_modalRealParts L lambda Delta rPlus rMinus =
        xi_qep_leakage_spectrum_commuting_criticalLines L lambda) ∧
    (0 < Delta →
      xi_qep_leakage_spectrum_commuting_modalRealParts L lambda Delta rPlus rMinus =
        xi_qep_leakage_spectrum_commuting_splitLines L rPlus rMinus) ∧
    (Delta < 0 ∨ Delta = 0 ∨ 0 < Delta)

/-- Paper label: `cor:xi-qep-leakage-spectrum-commuting`. -/
theorem paper_xi_qep_leakage_spectrum_commuting :
    xi_qep_leakage_spectrum_commuting_statement := by
  intro L alpha beta Delta rPlus rMinus
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hneg
    simp [xi_qep_leakage_spectrum_commuting_modalRealParts, le_of_lt hneg]
  · intro hzero
    simp [xi_qep_leakage_spectrum_commuting_modalRealParts, hzero]
  · intro hpos
    have hnot : ¬ Delta ≤ 0 := not_le.mpr hpos
    simp [xi_qep_leakage_spectrum_commuting_modalRealParts, hnot]
  · rcases lt_trichotomy Delta 0 with hlt | heq | hgt
    · exact Or.inl hlt
    · exact Or.inr (Or.inl heq)
    · exact Or.inr (Or.inr hgt)

end Omega.Zeta
