import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.Zeta

abbrev xi_time_part9gc_resolution_tower_haar_limit_layer (n : ℕ) :=
  ZMod (2 ^ (n + 1)) × ZMod (2 ^ (n + 1))

def xi_time_part9gc_resolution_tower_haar_limit_uniform_mass (n : ℕ) : ℚ :=
  1 / (4 : ℚ) ^ (n + 1)

def xi_time_part9gc_resolution_tower_haar_limit_cylinder_mass (n : ℕ)
    (_x : xi_time_part9gc_resolution_tower_haar_limit_layer n) : ℚ :=
  xi_time_part9gc_resolution_tower_haar_limit_uniform_mass n

def xi_time_part9gc_resolution_tower_haar_limit_compatible_family : Prop :=
  ∀ n, 4 * xi_time_part9gc_resolution_tower_haar_limit_uniform_mass (n + 1) =
    xi_time_part9gc_resolution_tower_haar_limit_uniform_mass n

def xi_time_part9gc_resolution_tower_haar_limit_uniform_cylinder_masses : Prop :=
  ∀ n (x : xi_time_part9gc_resolution_tower_haar_limit_layer n),
    xi_time_part9gc_resolution_tower_haar_limit_cylinder_mass n x =
      xi_time_part9gc_resolution_tower_haar_limit_uniform_mass n

def xi_time_part9gc_resolution_tower_haar_limit_is_haar_limit : Prop :=
  ∀ n (x t : xi_time_part9gc_resolution_tower_haar_limit_layer n),
    xi_time_part9gc_resolution_tower_haar_limit_cylinder_mass n (x + t) =
      xi_time_part9gc_resolution_tower_haar_limit_cylinder_mass n x

/-- `thm:xi-time-part9gc-resolution-tower-haar-limit` -/
theorem paper_xi_time_part9gc_resolution_tower_haar_limit :
    xi_time_part9gc_resolution_tower_haar_limit_compatible_family ∧
      xi_time_part9gc_resolution_tower_haar_limit_uniform_cylinder_masses ∧
      xi_time_part9gc_resolution_tower_haar_limit_is_haar_limit := by
  constructor
  · intro n
    rw [xi_time_part9gc_resolution_tower_haar_limit_uniform_mass,
      xi_time_part9gc_resolution_tower_haar_limit_uniform_mass]
    field_simp [pow_succ, pow_add, mul_assoc]
    ring
  · constructor
    · intro n x
      rfl
    · intro n x t
      rfl

end Omega.Zeta
