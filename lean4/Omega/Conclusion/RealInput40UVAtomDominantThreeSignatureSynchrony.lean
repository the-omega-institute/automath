import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.Conclusion.RealInput40UVAtomCore
import Omega.Conclusion.RealInput40UniquePrimitiveTwoStepAtom

namespace Omega.Conclusion

/-- Wrapper statement assembling the atom-dominant spectral split, the parity trace law with
spectral gap, and the delta-shell / primitive-atom signatures. -/
def conclusion_realinput40_uv_atom_dominant_three_signature_synchrony_statement : Prop :=
  (∀ rhoCore sqrtv : ℝ, rhoCore < sqrtv → max sqrtv rhoCore = sqrtv) ∧
    (∀ n : ℕ, ∀ ρ Λ₂ : ℝ, 0 < ρ → Λ₂ < ρ →
      ((Even n → (1 : ℤ) ^ n + (-1) ^ n = 2) ∧
        (Odd n → (1 : ℤ) ^ n + (-1) ^ n = 0) ∧
        0 < 1 - Λ₂ / ρ)) ∧
    (∀ n c r m : ℕ, 0 < m →
      (if n = 2 ∧ c = 0 ∧ r % m = 1 % m then 1 else 0 : ℕ) =
        (if n = 2 then 1 else 0) * (if c = 0 then 1 else 0) *
          (if r % m = 1 % m then 1 else 0)) ∧
    (∀ u : Complex,
      (∀ a : ℕ → Complex,
        conclusion_realinput40_unique_primitive_two_step_atom_admissible a u →
          a = conclusion_realinput40_unique_primitive_two_step_atom_canonical u) ∧
        (∀ n : ℕ,
          conclusion_realinput40_unique_primitive_two_step_atom_canonical u n =
            (if n = 2 then u else 0)) ∧
        conclusion_realinput40_unique_primitive_two_step_atom_branch_interpretation u)

/-- Paper label:
`thm:conclusion-realinput40-uv-atom-dominant-three-signature-synchrony`. -/
theorem paper_conclusion_realinput40_uv_atom_dominant_three_signature_synchrony :
    conclusion_realinput40_uv_atom_dominant_three_signature_synchrony_statement := by
  refine ⟨Omega.Conclusion.RealInput40UVAtomCore.atom_dominant_max,
    Omega.Conclusion.RealInput40UVAtomCore.paper_conclusion_realinput40_uv_atom_dominant_trace_law,
    Omega.Conclusion.RealInput40UVAtomCore.delta_shell_indicator, ?_⟩
  intro u
  exact paper_conclusion_realinput40_unique_primitive_two_step_atom u

end Omega.Conclusion
