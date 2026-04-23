import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- The angular scale `t_m = 2π / m`. -/
noncomputable def near1_pole_diffusive_sp_t (m : ℕ) : ℝ :=
  2 * Real.pi / m

/-- The normalized near-`1` singularity `s_m = P₂(it_m) / log λ`. -/
noncomputable def near1_pole_diffusive_sp_s (P₂ : ℝ → ℂ) (lam : ℝ) (m : ℕ) : ℂ :=
  P₂ (near1_pole_diffusive_sp_t m) / Real.log lam

/-- Paper-facing near-`1` pole statement: once the pure-imaginary pressure slice is expanded at the
dyadic scales `t_m`, the normalized points `s_m` and their real/imaginary parts follow by direct
algebra. -/
def near1_pole_diffusive_sp_statement : Prop :=
  ∀ (P₂ : ℝ → ℂ) (lam mu2 sigma2Sq : ℝ) (ε : ℕ → ℂ), 1 < lam →
    (∀ m : ℕ, 2 ≤ m →
      P₂ (near1_pole_diffusive_sp_t m) =
        Real.log lam + (mu2 * near1_pole_diffusive_sp_t m) * Complex.I -
          (sigma2Sq / 2) * (near1_pole_diffusive_sp_t m) ^ 2 + ε m) →
      (∀ m : ℕ, 2 ≤ m →
        near1_pole_diffusive_sp_s P₂ lam m =
          1 + ((mu2 / Real.log lam) * near1_pole_diffusive_sp_t m) * Complex.I -
            (sigma2Sq / (2 * Real.log lam)) * (near1_pole_diffusive_sp_t m) ^ 2 +
            ε m / Real.log lam) ∧
      (∀ m : ℕ, 2 ≤ m →
        Complex.re (near1_pole_diffusive_sp_s P₂ lam m) =
          Complex.re
            (1 + ((mu2 / Real.log lam) * near1_pole_diffusive_sp_t m) * Complex.I -
              (sigma2Sq / (2 * Real.log lam)) * (near1_pole_diffusive_sp_t m) ^ 2 +
              ε m / Real.log lam)) ∧
      (∀ m : ℕ, 2 ≤ m →
        Complex.im (near1_pole_diffusive_sp_s P₂ lam m) =
          Complex.im
            (1 + ((mu2 / Real.log lam) * near1_pole_diffusive_sp_t m) * Complex.I -
              (sigma2Sq / (2 * Real.log lam)) * (near1_pole_diffusive_sp_t m) ^ 2 +
              ε m / Real.log lam))

theorem paper_near1_pole_diffusive_sp : near1_pole_diffusive_sp_statement := by
  intro P₂ lam mu2 sigma2Sq ε hlam hP₂
  have hlog_pos : 0 < Real.log lam := Real.log_pos hlam
  have hlog_ne : (Real.log lam : ℂ) ≠ 0 := by
    exact_mod_cast hlog_pos.ne'
  have hs :
      ∀ m : ℕ, 2 ≤ m →
        near1_pole_diffusive_sp_s P₂ lam m =
          1 + ((mu2 / Real.log lam) * near1_pole_diffusive_sp_t m) * Complex.I -
            (sigma2Sq / (2 * Real.log lam)) * (near1_pole_diffusive_sp_t m) ^ 2 +
            ε m / Real.log lam := by
    intro m hm
    unfold near1_pole_diffusive_sp_s
    rw [hP₂ m hm]
    field_simp [hlog_ne]
  refine ⟨hs, ?_, ?_⟩
  · intro m hm
    simpa using congrArg Complex.re (hs m hm)
  · intro m hm
    simpa using congrArg Complex.im (hs m hm)

end Omega.Zeta
