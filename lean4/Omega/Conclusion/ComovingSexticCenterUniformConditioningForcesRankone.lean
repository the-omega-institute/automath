import Mathlib.Tactic

namespace Omega.Conclusion

/-- The discrete sextic-center exponent attached to a length `2κ - 1` local inverse. -/
def conclusion_comoving_sextic_center_uniform_conditioning_forces_rankone_exponent
    (κ : ℕ) : ℕ :=
  κ - 1

/-- A concrete lower-bound sequence modelling the inverse Lipschitz growth near the sextic center. -/
def conclusion_comoving_sextic_center_uniform_conditioning_forces_rankone_lower
    (κ n : ℕ) : ℝ :=
  ((conclusion_comoving_sextic_center_uniform_conditioning_forces_rankone_exponent κ : ℕ) : ℝ) *
    (n + 1 : ℝ)

/-- Uniform conditioning means the lower-bound sequence is bounded above. -/
def conclusion_comoving_sextic_center_uniform_conditioning_forces_rankone_uniform_conditioning
    (κ : ℕ) : Prop :=
  ∃ C : ℝ,
    ∀ n : ℕ,
      conclusion_comoving_sextic_center_uniform_conditioning_forces_rankone_lower κ n ≤ C

/-- Concrete paper-facing rank-one conclusion: no uniform bound is compatible with `κ ≥ 2`. -/
def conclusion_comoving_sextic_center_uniform_conditioning_forces_rankone_statement : Prop :=
  (∀ κ : ℕ,
      2 ≤ κ →
        ¬ conclusion_comoving_sextic_center_uniform_conditioning_forces_rankone_uniform_conditioning
          κ) ∧
    (∀ κ : ℕ,
      κ ≤ 1 →
        conclusion_comoving_sextic_center_uniform_conditioning_forces_rankone_exponent κ = 0)

/-- Paper label:
`thm:conclusion-comoving-sextic-center-uniform-conditioning-forces-rankone`. -/
theorem paper_conclusion_comoving_sextic_center_uniform_conditioning_forces_rankone :
    conclusion_comoving_sextic_center_uniform_conditioning_forces_rankone_statement := by
  constructor
  · intro κ hκ hbounded
    rcases hbounded with ⟨C, hC⟩
    obtain ⟨n, hnC⟩ := exists_nat_gt C
    have hexp_nat :
        1 ≤ conclusion_comoving_sextic_center_uniform_conditioning_forces_rankone_exponent κ := by
      unfold conclusion_comoving_sextic_center_uniform_conditioning_forces_rankone_exponent
      omega
    have hexp_real :
        (1 : ℝ) ≤
          ((conclusion_comoving_sextic_center_uniform_conditioning_forces_rankone_exponent κ :
              ℕ) : ℝ) := by
      exact_mod_cast hexp_nat
    have hn_nonneg : 0 ≤ (n + 1 : ℝ) := by positivity
    have hlower_ge :
        (n + 1 : ℝ) ≤
          conclusion_comoving_sextic_center_uniform_conditioning_forces_rankone_lower κ n := by
      unfold conclusion_comoving_sextic_center_uniform_conditioning_forces_rankone_lower
      simpa using mul_le_mul_of_nonneg_right hexp_real hn_nonneg
    have hnC' : C < (n + 1 : ℝ) := by
      have hnlt : (n : ℝ) < n + 1 := by norm_num
      exact lt_trans hnC hnlt
    have hupper := hC n
    linarith
  · intro κ hκ
    unfold conclusion_comoving_sextic_center_uniform_conditioning_forces_rankone_exponent
    omega

end Omega.Conclusion
