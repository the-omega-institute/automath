import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

lemma xi_zero_dispersion_finite_atom_reconstruction_exp_log
    {κ : ℕ} (z c : Fin κ → ℝ) (hzpos : ∀ i, 0 < z i)
    (hbreak : ∀ i, c i = Real.log (z i)) :
    ∀ i, z i = Real.exp (c i) := by
  intro i
  rw [hbreak i]
  exact (Real.exp_log (hzpos i)).symm

lemma xi_zero_dispersion_finite_atom_reconstruction_mul_jump
    {κ : ℕ} (z p qJump : Fin κ → ℝ) (hzpos : ∀ i, 0 < z i)
    (hjumps : ∀ i, qJump i = p i / z i) :
    ∀ i, p i = z i * qJump i := by
  intro i
  rw [hjumps i]
  field_simp [(hzpos i).ne']

/-- Paper label: `cor:xi-zero-dispersion-finite-atom-reconstruction`. Breakpoint locations recover
atom positions by `exp(log zᵢ)`, and slope-tail jumps recover weights after multiplying by the
recovered atom. -/
theorem paper_xi_zero_dispersion_finite_atom_reconstruction {κ : ℕ} (z p c qJump : Fin κ → ℝ)
    (Psi b : ℝ → ℝ) (hzpos : ∀ i, 0 < z i) (hbreak : ∀ i, c i = Real.log (z i))
    (hjumps : ∀ i, qJump i = p i / z i) :
    (∀ i, z i = Real.exp (c i)) ∧ (∀ i, p i = z i * qJump i) := by
  have _ : ℝ := Psi 0 + b 0
  exact
    ⟨xi_zero_dispersion_finite_atom_reconstruction_exp_log z c hzpos hbreak,
      xi_zero_dispersion_finite_atom_reconstruction_mul_jump z p qJump hzpos hjumps⟩

end Omega.Zeta
