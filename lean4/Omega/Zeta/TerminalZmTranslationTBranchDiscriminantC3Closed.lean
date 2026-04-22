import Mathlib.Tactic

namespace Omega.Zeta

/-- Closed-form branch discriminant polynomial from
`thm:xi-terminal-zm-translation-t-branch-discriminant-c3-closed`, viewed over the integer
coefficient ring. -/
def xi_terminal_zm_translation_t_branch_discriminant_c3_closed_D (t u : ℤ) : ℤ :=
  -27 * u ^ 11 + 90 * t * u ^ 9 + (4 * t ^ 3 - 22) * u ^ 8 - 239 * t ^ 2 * u ^ 7 -
    (8 * t ^ 4 + 70 * t) * u ^ 6 + (236 * t ^ 3 + 5) * u ^ 5 +
    (20 * t ^ 5 - 164 * t ^ 2) * u ^ 4 - (120 * t ^ 4 + 108 * t) * u ^ 3 +
    220 * t ^ 3 * u ^ 2 - 120 * t ^ 2 * u + 20 * t

/-- Displayed closed-form coefficient formula for the discriminant polynomial. -/
abbrev xi_terminal_zm_translation_t_branch_discriminant_c3_closed_rhs : ℤ → ℤ → ℤ :=
  xi_terminal_zm_translation_t_branch_discriminant_c3_closed_D

/-- The same closed formula evaluated over an arbitrary commutative ring. -/
def xi_terminal_zm_translation_t_branch_discriminant_c3_closed_eval {R : Type*} [CommRing R]
    (t u : R) : R :=
  -27 * u ^ 11 + 90 * t * u ^ 9 + (4 * t ^ 3 - 22) * u ^ 8 - 239 * t ^ 2 * u ^ 7 -
    (8 * t ^ 4 + 70 * t) * u ^ 6 + (236 * t ^ 3 + 5) * u ^ 5 +
    (20 * t ^ 5 - 164 * t ^ 2) * u ^ 4 - (120 * t ^ 4 + 108 * t) * u ^ 3 +
    220 * t ^ 3 * u ^ 2 - 120 * t ^ 2 * u + 20 * t

/-- Concrete `C₃` covariance relation for the closed discriminant formula. -/
def xi_terminal_zm_translation_t_branch_discriminant_c3_closed_covariant : Prop :=
  ∀ ζ t u : ℂ, ζ ^ 3 = 1 →
    xi_terminal_zm_translation_t_branch_discriminant_c3_closed_eval (ζ * t) u =
      ζ * xi_terminal_zm_translation_t_branch_discriminant_c3_closed_eval t (ζ * u)

/-- Closed-form formula and its `C₃` covariance under `(t, u) ↦ (ζ t, ζ u)`. -/
theorem paper_xi_terminal_zm_translation_t_branch_discriminant_c3_closed :
    xi_terminal_zm_translation_t_branch_discriminant_c3_closed_D =
      xi_terminal_zm_translation_t_branch_discriminant_c3_closed_rhs ∧
    xi_terminal_zm_translation_t_branch_discriminant_c3_closed_covariant := by
  refine ⟨rfl, ?_⟩
  intro ζ t u hζ
  have hζ4 : ζ ^ 4 = ζ := by
    calc
      ζ ^ 4 = ζ ^ (3 + 1) := by norm_num
      _ = ζ ^ 3 * ζ := by simpa using (pow_succ ζ 3)
      _ = ζ := by simp [hζ]
  have hζ5 : ζ ^ 5 = ζ ^ 2 := by
    calc
      ζ ^ 5 = ζ ^ (3 + 2) := by norm_num
      _ = ζ ^ 3 * ζ ^ 2 := by rw [pow_add]
      _ = ζ ^ 2 := by simp [hζ]
  have hζ6 : ζ ^ 6 = 1 := by
    calc
      ζ ^ 6 = ζ ^ (3 * 2) := by norm_num
      _ = (ζ ^ 3) ^ 2 := by rw [pow_mul]
      _ = 1 := by simp [hζ]
  have hζ7 : ζ ^ 7 = ζ := by
    calc
      ζ ^ 7 = ζ ^ (6 + 1) := by norm_num
      _ = ζ ^ 6 * ζ := by simpa using (pow_succ ζ 6)
      _ = ζ := by simp [hζ6]
  have hζ8 : ζ ^ 8 = ζ ^ 2 := by
    calc
      ζ ^ 8 = ζ ^ (6 + 2) := by norm_num
      _ = ζ ^ 6 * ζ ^ 2 := by rw [pow_add]
      _ = ζ ^ 2 := by simp [hζ6]
  have hζ9 : ζ ^ 9 = 1 := by
    calc
      ζ ^ 9 = ζ ^ (3 * 3) := by norm_num
      _ = (ζ ^ 3) ^ 3 := by rw [pow_mul]
      _ = 1 := by simp [hζ]
  have hζ10 : ζ ^ 10 = ζ := by
    calc
      ζ ^ 10 = ζ ^ (9 + 1) := by norm_num
      _ = ζ ^ 9 * ζ := by simpa using (pow_succ ζ 9)
      _ = ζ := by simp [hζ9]
  have hζ11 : ζ ^ 11 = ζ ^ 2 := by
    calc
      ζ ^ 11 = ζ ^ (9 + 2) := by norm_num
      _ = ζ ^ 9 * ζ ^ 2 := by rw [pow_add]
      _ = ζ ^ 2 := by simp [hζ9]
  have hζ12 : ζ ^ 12 = 1 := by
    calc
      ζ ^ 12 = ζ ^ (3 * 4) := by norm_num
      _ = (ζ ^ 3) ^ 4 := by rw [pow_mul]
      _ = 1 := by simp [hζ]
  unfold xi_terminal_zm_translation_t_branch_discriminant_c3_closed_eval
  ring_nf
  simp [hζ, hζ4, hζ5, hζ6, hζ7, hζ8, hζ9, hζ10, hζ12]

end Omega.Zeta
