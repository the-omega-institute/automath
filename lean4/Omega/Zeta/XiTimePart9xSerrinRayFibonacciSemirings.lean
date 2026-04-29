import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.Zeta

set_option linter.unusedVariables false

/-- The integer scale coordinate of the centered Wulff ray. -/
abbrev xi_time_part9x_serrin_ray_fibonacci_semirings_scaleRay := ℕ

/-- The Fibonacci modulus seen at finite resolution `m`. -/
def xi_time_part9x_serrin_ray_fibonacci_semirings_modulus (m : ℕ) : ℕ :=
  Nat.fib (m + 2)

/-- The residue of a Wulff scale at resolution `m`. -/
def xi_time_part9x_serrin_ray_fibonacci_semirings_residue (m : ℕ)
    (ρ : xi_time_part9x_serrin_ray_fibonacci_semirings_scaleRay) :
    ZMod (xi_time_part9x_serrin_ray_fibonacci_semirings_modulus m) :=
  ρ

/-- Finite resolution operations are the transported operations on the Fibonacci residue ring. -/
def xi_time_part9x_serrin_ray_fibonacci_semirings_finite_resolution_isomorphism
    (m : ℕ) : Prop :=
  (∀ ρ σ,
      xi_time_part9x_serrin_ray_fibonacci_semirings_residue m (ρ + σ) =
        xi_time_part9x_serrin_ray_fibonacci_semirings_residue m ρ +
          xi_time_part9x_serrin_ray_fibonacci_semirings_residue m σ) ∧
    ∀ ρ σ,
      xi_time_part9x_serrin_ray_fibonacci_semirings_residue m (ρ * σ) =
        xi_time_part9x_serrin_ray_fibonacci_semirings_residue m ρ *
          xi_time_part9x_serrin_ray_fibonacci_semirings_residue m σ

/-- The Grothendieck completion of the additive scale ray is represented by integer scales. -/
def xi_time_part9x_serrin_ray_fibonacci_semirings_grothendieck_completion : Prop :=
  (∀ ρ σ : xi_time_part9x_serrin_ray_fibonacci_semirings_scaleRay,
      ((ρ + σ : ℕ) : ℤ) = (ρ : ℤ) + (σ : ℤ)) ∧
    ∀ ρ σ : xi_time_part9x_serrin_ray_fibonacci_semirings_scaleRay,
      ((ρ : ℤ) - (σ : ℤ)) + (σ : ℤ) = (ρ : ℤ)

/-- Fibonacci-adic congruent scale changes vanish in every finite residue quotient. -/
def xi_time_part9x_serrin_ray_fibonacci_semirings_fibonacci_completion (m : ℕ) : Prop :=
  ∀ ρ k : xi_time_part9x_serrin_ray_fibonacci_semirings_scaleRay,
    xi_time_part9x_serrin_ray_fibonacci_semirings_residue m
        (ρ + k * xi_time_part9x_serrin_ray_fibonacci_semirings_modulus m) =
      xi_time_part9x_serrin_ray_fibonacci_semirings_residue m ρ

/-- Paper label: `thm:xi-time-part9x-serrin-ray-fibonacci-semirings`. -/
theorem paper_xi_time_part9x_serrin_ray_fibonacci_semirings (m : ℕ) (hm : 1 ≤ m) :
    xi_time_part9x_serrin_ray_fibonacci_semirings_finite_resolution_isomorphism m ∧
      xi_time_part9x_serrin_ray_fibonacci_semirings_grothendieck_completion ∧
      xi_time_part9x_serrin_ray_fibonacci_semirings_fibonacci_completion m := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro ρ σ
      simp [xi_time_part9x_serrin_ray_fibonacci_semirings_residue]
    · intro ρ σ
      simp [xi_time_part9x_serrin_ray_fibonacci_semirings_residue]
  · constructor
    · intro ρ σ
      norm_num
    · intro ρ σ
      omega
  · intro ρ k
    simp [xi_time_part9x_serrin_ray_fibonacci_semirings_residue,
      xi_time_part9x_serrin_ray_fibonacci_semirings_modulus]

end Omega.Zeta
