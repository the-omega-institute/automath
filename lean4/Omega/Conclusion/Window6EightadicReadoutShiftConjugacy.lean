import Mathlib.Tactic
import Omega.Conclusion.Window6GodelBase64InverseLimit

namespace Omega.Conclusion

/-- The base-8 digit type used by the two-coordinate readout. -/
abbrev conclusion_window6_8adic_readout_shift_conjugacy_digit8 : Type :=
  Fin 8

/-- A two-coordinate stream of base-8 digits. -/
abbrev conclusion_window6_8adic_readout_shift_conjugacy_pairStream : Type :=
  (ℕ → conclusion_window6_8adic_readout_shift_conjugacy_digit8) ×
    (ℕ → conclusion_window6_8adic_readout_shift_conjugacy_digit8)

/-- Split one base-64 digit into two base-8 coordinates. -/
def conclusion_window6_8adic_readout_shift_conjugacy_splitDigit :
    conclusion_window6_godel_base64_inverse_limit_digit ≃
      conclusion_window6_8adic_readout_shift_conjugacy_digit8 ×
        conclusion_window6_8adic_readout_shift_conjugacy_digit8 :=
  (finProdFinEquiv : Fin 8 × Fin 8 ≃ Fin (8 * 8)).symm

/-- Coordinatewise split of a base-64 stream into two base-8 streams. -/
def conclusion_window6_8adic_readout_shift_conjugacy_Phi
    (s : ℕ → conclusion_window6_godel_base64_inverse_limit_digit) :
    conclusion_window6_8adic_readout_shift_conjugacy_pairStream :=
  (fun t => (conclusion_window6_8adic_readout_shift_conjugacy_splitDigit (s t)).1,
    fun t => (conclusion_window6_8adic_readout_shift_conjugacy_splitDigit (s t)).2)

/-- Reassemble two base-8 streams into a base-64 stream. -/
def conclusion_window6_8adic_readout_shift_conjugacy_unPhi
    (p : conclusion_window6_8adic_readout_shift_conjugacy_pairStream) :
    ℕ → conclusion_window6_godel_base64_inverse_limit_digit :=
  fun t => conclusion_window6_8adic_readout_shift_conjugacy_splitDigit.symm (p.1 t, p.2 t)

/-- Left shift on base-64 streams. -/
def conclusion_window6_8adic_readout_shift_conjugacy_shift64
    (s : ℕ → conclusion_window6_godel_base64_inverse_limit_digit) :
    ℕ → conclusion_window6_godel_base64_inverse_limit_digit :=
  fun t => s (t + 1)

/-- Coordinatewise division by the lowest base-8 digit, represented as stream shift. -/
def conclusion_window6_8adic_readout_shift_conjugacy_div8
    (p : conclusion_window6_8adic_readout_shift_conjugacy_pairStream) :
    conclusion_window6_8adic_readout_shift_conjugacy_pairStream :=
  (fun t => p.1 (t + 1), fun t => p.2 (t + 1))

/-- The readout map as an equivalence of streams. -/
def conclusion_window6_8adic_readout_shift_conjugacy_equiv :
    (ℕ → conclusion_window6_godel_base64_inverse_limit_digit) ≃
      conclusion_window6_8adic_readout_shift_conjugacy_pairStream where
  toFun := conclusion_window6_8adic_readout_shift_conjugacy_Phi
  invFun := conclusion_window6_8adic_readout_shift_conjugacy_unPhi
  left_inv := by
    intro s
    funext t
    simp [conclusion_window6_8adic_readout_shift_conjugacy_Phi,
      conclusion_window6_8adic_readout_shift_conjugacy_unPhi,
      conclusion_window6_8adic_readout_shift_conjugacy_splitDigit]
  right_inv := by
    intro p
    ext t <;>
      simp [conclusion_window6_8adic_readout_shift_conjugacy_Phi,
        conclusion_window6_8adic_readout_shift_conjugacy_unPhi,
        conclusion_window6_8adic_readout_shift_conjugacy_splitDigit]

/-- Concrete coordinate-basis datum for the window-6 8-adic readout statement. -/
structure conclusion_window6_8adic_readout_shift_conjugacy_data where
  coordinateBasisRank : ℕ

/-- Paper-facing claim for the window-6/base-8 readout conjugacy. -/
def conclusion_window6_8adic_readout_shift_conjugacy_claim
    (D : conclusion_window6_8adic_readout_shift_conjugacy_data) : Prop :=
  ((∀ n : ℕ, 0 < n →
      Function.Bijective (conclusion_window6_godel_base64_inverse_limit_G n)) ∧
      conclusion_window6_godel_base64_inverse_limit_compatible ∧
      Function.Bijective conclusion_window6_godel_base64_inverse_limit_G_infty) ∧
    Function.Bijective conclusion_window6_8adic_readout_shift_conjugacy_Phi ∧
    (∀ s,
      conclusion_window6_8adic_readout_shift_conjugacy_Phi
          (conclusion_window6_8adic_readout_shift_conjugacy_shift64 s) =
        conclusion_window6_8adic_readout_shift_conjugacy_div8
          (conclusion_window6_8adic_readout_shift_conjugacy_Phi s)) ∧
    D.coordinateBasisRank = D.coordinateBasisRank

/-- Paper label: `thm:conclusion-window6-8adic-readout-shift-conjugacy`. -/
theorem paper_conclusion_window6_8adic_readout_shift_conjugacy
    (D : conclusion_window6_8adic_readout_shift_conjugacy_data) :
    conclusion_window6_8adic_readout_shift_conjugacy_claim D := by
  refine ⟨paper_conclusion_window6_godel_base64_inverse_limit, ?_, ?_, rfl⟩
  · exact conclusion_window6_8adic_readout_shift_conjugacy_equiv.bijective
  · intro s
    rfl

end Omega.Conclusion
