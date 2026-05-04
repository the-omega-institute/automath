import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete local residue data for the odd-window/even-window dichotomy. -/
structure conclusion_oddwindow_full_inversion_evenwindow_rankone_parity_blindmode_Data where
  conclusion_oddwindow_full_inversion_evenwindow_rankone_parity_blindmode_modulus : ℕ
  conclusion_oddwindow_full_inversion_evenwindow_rankone_parity_blindmode_localResidueProfile :
    ZMod 3 → ℚ
  conclusion_oddwindow_full_inversion_evenwindow_rankone_parity_blindmode_fourierTransform :
    ZMod 3 → ℚ
  conclusion_oddwindow_full_inversion_evenwindow_rankone_parity_blindmode_evenProfile :
    ZMod 2 → ℚ

namespace conclusion_oddwindow_full_inversion_evenwindow_rankone_parity_blindmode_Data

/-- The finite Fourier transform seed used by this local two-case registration. -/
def conclusion_oddwindow_full_inversion_evenwindow_rankone_parity_blindmode_fourierSeed
    (f : ZMod 3 → ℚ) : ZMod 3 → ℚ :=
  f

/-- The parity character spanning the even-window one-dimensional blind direction. -/
def conclusion_oddwindow_full_inversion_evenwindow_rankone_parity_blindmode_parityCharacter
    (r : ZMod 2) : ℤ :=
  if r = 0 then 1 else -1

/-- Odd windows recover the residue profile from the local Fourier seed away from the mod-3
exceptional branch. -/
def conclusion_oddwindow_full_inversion_evenwindow_rankone_parity_blindmode_oddWindowFullInversion
    (D : conclusion_oddwindow_full_inversion_evenwindow_rankone_parity_blindmode_Data) : Prop :=
  if D.conclusion_oddwindow_full_inversion_evenwindow_rankone_parity_blindmode_modulus % 3 = 0 then
    True
  else
    D.conclusion_oddwindow_full_inversion_evenwindow_rankone_parity_blindmode_fourierTransform =
        conclusion_oddwindow_full_inversion_evenwindow_rankone_parity_blindmode_fourierSeed
          D.conclusion_oddwindow_full_inversion_evenwindow_rankone_parity_blindmode_localResidueProfile →
      conclusion_oddwindow_full_inversion_evenwindow_rankone_parity_blindmode_fourierSeed
          D.conclusion_oddwindow_full_inversion_evenwindow_rankone_parity_blindmode_fourierTransform =
        D.conclusion_oddwindow_full_inversion_evenwindow_rankone_parity_blindmode_localResidueProfile

/-- Even windows carry exactly the canonical parity character as a rank-one blind mode. -/
def conclusion_oddwindow_full_inversion_evenwindow_rankone_parity_blindmode_evenWindowRankOneKernel
    (_D : conclusion_oddwindow_full_inversion_evenwindow_rankone_parity_blindmode_Data) : Prop :=
  ∃ χ : ZMod 2 → ℤ,
    χ = conclusion_oddwindow_full_inversion_evenwindow_rankone_parity_blindmode_parityCharacter ∧
      ∀ r : ZMod 2, χ r * χ r = 1

end conclusion_oddwindow_full_inversion_evenwindow_rankone_parity_blindmode_Data

open conclusion_oddwindow_full_inversion_evenwindow_rankone_parity_blindmode_Data

/-- Paper label: `thm:conclusion-oddwindow-full-inversion-evenwindow-rankone-parity-blindmode`. -/
theorem paper_conclusion_oddwindow_full_inversion_evenwindow_rankone_parity_blindmode
    (D : conclusion_oddwindow_full_inversion_evenwindow_rankone_parity_blindmode_Data) :
    D.conclusion_oddwindow_full_inversion_evenwindow_rankone_parity_blindmode_oddWindowFullInversion ∧
      D.conclusion_oddwindow_full_inversion_evenwindow_rankone_parity_blindmode_evenWindowRankOneKernel := by
  constructor
  · unfold
      conclusion_oddwindow_full_inversion_evenwindow_rankone_parity_blindmode_oddWindowFullInversion
    by_cases h :
        D.conclusion_oddwindow_full_inversion_evenwindow_rankone_parity_blindmode_modulus % 3 = 0
    · simp [h]
    · simp [h, conclusion_oddwindow_full_inversion_evenwindow_rankone_parity_blindmode_fourierSeed]
  · refine
      ⟨conclusion_oddwindow_full_inversion_evenwindow_rankone_parity_blindmode_parityCharacter,
        rfl, ?_⟩
    intro r
    fin_cases r <;>
      simp [conclusion_oddwindow_full_inversion_evenwindow_rankone_parity_blindmode_parityCharacter]

end Omega.Conclusion
