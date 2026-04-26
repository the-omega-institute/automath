import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.CircleDimension.RoseLaurentCharacterFiniteSingularRing

namespace Omega.CircleDimension

noncomputable section

/-- The Laurent rose map viewed as the image-plane branch map. -/
noncomputable def derived_rose_image_branch_ring_map (d n : ℕ) (w : ℂ) : ℂ :=
  roseLaurentCharacter d n w

/-- The parameter-ring radius coming from the critical equation
`(d + n) w^(2n) + (d - n) = 0`. -/
noncomputable def derived_rose_image_branch_ring_parameter_radius (d n : ℕ) : ℝ :=
  (((d - n : ℝ) / (d + n : ℝ)) ^ ((1 : ℝ) / (2 * n : ℝ)))

/-- The image-plane branch-ring radius obtained by substituting the critical equation back into
the rose map and then taking norms. -/
noncomputable def derived_rose_image_branch_ring_radius (d n : ℕ) : ℝ :=
  (n : ℝ) / (d + n : ℝ) *
    derived_rose_image_branch_ring_parameter_radius d n ^ (d - n)

/-- If a critical point lies on the parameter singular ring, then its rose-image branch value has
the common modulus `R_{n,d}`. -/
def derived_rose_image_branch_ring_statement (d n : ℕ) : Prop :=
  1 ≤ n →
    n < d →
      ∀ w : ℂ,
        ((d + n : ℂ) * w ^ (2 * n) + (d - n : ℂ) = 0) →
        ‖w‖ = derived_rose_image_branch_ring_parameter_radius d n →
        ‖derived_rose_image_branch_ring_map d n w‖ = derived_rose_image_branch_ring_radius d n

/-- Paper label: `thm:derived-rose-image-branch-ring`. -/
theorem paper_derived_rose_image_branch_ring (d n : ℕ) :
    derived_rose_image_branch_ring_statement d n := by
  intro hn hdn w hcrit hw
  have hring := paper_cdim_rose_laurent_character_finite_singular_ring d n hdn hn
  have hdn_pos : 0 < d := lt_of_le_of_lt (Nat.zero_le n) hdn
  have hden : ((d + n : ℂ)) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.add_pos_left hdn_pos n))
  have hsolve : w ^ (2 * n) = -((d - n : ℂ) / (d + n : ℂ)) := by
    have hneg : (d + n : ℂ) * w ^ (2 * n) = -(d - n : ℂ) := by
      exact eq_neg_of_add_eq_zero_left hcrit
    calc
      w ^ (2 * n) = ((d + n : ℂ) * w ^ (2 * n)) / (d + n : ℂ) := by
          field_simp [hden]
      _ = ((n : ℂ) - d) / (d + n : ℂ) := by
            simpa [sub_eq_add_neg] using congrArg (fun z => z / (d + n : ℂ)) hneg
      _ = -((d - n : ℂ) / (d + n : ℂ)) := by ring
  have hfactor :
      w ^ (2 * n) + 1 = ((2 * n : ℂ) / (d + n : ℂ)) := by
    rw [hsolve]
    field_simp [hden]
    ring
  have hmap :
      derived_rose_image_branch_ring_map d n w = ((n : ℂ) / (d + n : ℂ)) * w ^ (d - n) := by
    have hfac := hring.1 w
    calc
      derived_rose_image_branch_ring_map d n w
          = roseLaurentCharacter d n w := by rfl
      _ = (1 / 2 : ℂ) * (w ^ (d - n) * (w ^ (2 * n) + 1)) := by
            rw [← hfac]
            ring
      _ = (1 / 2 : ℂ) * (w ^ (d - n) * ((2 * n : ℂ) / (d + n : ℂ))) := by rw [hfactor]
      _ = w ^ (d - n) * ((n : ℂ) / (d + n : ℂ)) := by
            field_simp [hden]
      _ = ((n : ℂ) / (d + n : ℂ)) * w ^ (d - n) := by ring
  have hconst :
      ‖((n : ℂ) / (d + n : ℂ))‖ = (n : ℝ) / (d + n : ℝ) := by
    have hnonneg : 0 ≤ (d + n : ℝ) := by positivity
    have hnum : ‖(n : ℂ)‖ = (n : ℝ) := by norm_num
    have hden_real : ‖((d + n : ℂ))‖ = |(d + n : ℝ)| := by
      simpa using Complex.norm_real (d + n : ℝ)
    calc
      ‖((n : ℂ) / (d + n : ℂ))‖ = ‖(n : ℂ)‖ / ‖((d + n : ℂ))‖ := norm_div _ _
      _ = (n : ℝ) / |(d + n : ℝ)| := by rw [hnum, hden_real]
      _ = (n : ℝ) / (d + n : ℝ) := by simp [abs_of_nonneg hnonneg]
  calc
    ‖derived_rose_image_branch_ring_map d n w‖
        = ‖(n : ℂ) / (d + n : ℂ)‖ * ‖w ^ (d - n)‖ := by
            rw [hmap, norm_mul]
    _ = (n : ℝ) / (d + n : ℝ) * ‖w‖ ^ (d - n) := by
          rw [hconst, norm_pow]
    _ = derived_rose_image_branch_ring_radius d n := by
          simp [derived_rose_image_branch_ring_radius, hw]

end

end Omega.CircleDimension
