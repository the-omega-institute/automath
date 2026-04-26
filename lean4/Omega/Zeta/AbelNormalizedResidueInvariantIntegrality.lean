import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:abel-normalized-residue-invariant-integrality`. Dividing the raw residue
identity by the nonzero pole exactly recovers the normalized residue certificate, and multiplying
that certificate back by the pole reconstructs the raw residue law. -/
theorem paper_abel_normalized_residue_invariant_integrality (rho pole rawResidue : ℂ)
    (hpole : pole ≠ 0) :
    (∃ m : ℕ, 0 < m ∧ rawResidue = (m : ℂ) * pole / rho) ↔
      ∃ m : ℕ, 0 < m ∧ rawResidue / pole = (m : ℂ) / rho := by
  constructor
  · rintro ⟨m, hm, hraw⟩
    refine ⟨m, hm, ?_⟩
    calc
      rawResidue / pole = (((m : ℂ) * pole) / rho) / pole := by rw [hraw]
      _ = (m : ℂ) / rho := by
        simp [div_eq_mul_inv, hpole, mul_left_comm, mul_comm]
  · rintro ⟨m, hm, hnorm⟩
    refine ⟨m, hm, ?_⟩
    have hmul : (rawResidue / pole) * pole = ((m : ℂ) / rho) * pole := by
      exact congrArg (fun z : ℂ => z * pole) hnorm
    calc
      rawResidue = (rawResidue / pole) * pole := by
        simp [div_eq_mul_inv, hpole]
      _ = ((m : ℂ) / rho) * pole := hmul
      _ = (m : ℂ) * pole / rho := by
        simp [div_eq_mul_inv, mul_left_comm, mul_comm]

end Omega.Zeta
