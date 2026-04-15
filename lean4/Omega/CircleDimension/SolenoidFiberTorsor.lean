import Mathlib.Tactic

namespace Omega.CircleDimension

variable {G H : Type*} [Group G] [Group H]

/-- Same-fiber quotient is in the kernel.
    cor:cdim-solenoid-fiber-torsor -/
theorem same_fiber_inv_mul_mem_ker (f : G →* H) (x y : G) (hxy : f x = f y) :
    x⁻¹ * y ∈ f.ker := by
  rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]

/-- Translating a fiber element by a kernel element stays in the same fiber.
    cor:cdim-solenoid-fiber-torsor -/
theorem mul_ker_same_fiber (f : G →* H) (x k : G) (hk : k ∈ f.ker) :
    f (x * k) = f x := by
  have hk1 : f k = 1 := MonoidHom.mem_ker.mp hk
  rw [map_mul, hk1, mul_one]

/-- Each pair of same-fiber elements has a unique kernel witness of
    their quotient.
    cor:cdim-solenoid-fiber-torsor -/
theorem fiber_torsor_unique (f : G →* H) (x y : G) (hxy : f x = f y) :
    ∃! k : G, k ∈ f.ker ∧ y = x * k := by
  refine ⟨x⁻¹ * y, ⟨same_fiber_inv_mul_mem_ker f x y hxy, ?_⟩, ?_⟩
  · group
  · rintro k ⟨_, hk_eq⟩
    have : k = x⁻¹ * y := by rw [hk_eq]; group
    exact this

/-- Existence: any `x` plus any kernel element gives a same-fiber partner.
    cor:cdim-solenoid-fiber-torsor -/
theorem fiber_torsor_exists (f : G →* H) (x k : G) (hk : k ∈ f.ker) :
    ∃ y : G, f y = f x ∧ y = x * k :=
  ⟨x * k, mul_ker_same_fiber f x k hk, rfl⟩

/-- Paper package: solenoid fibers as principal homogeneous spaces over
    the kernel of the projection homomorphism.
    cor:cdim-solenoid-fiber-torsor -/
theorem paper_cdim_solenoid_fiber_torsor :
    (∀ (f : G →* H) (x y : G), f x = f y → x⁻¹ * y ∈ f.ker) ∧
    (∀ (f : G →* H) (x k : G), k ∈ f.ker → f (x * k) = f x) ∧
    (∀ (f : G →* H) (x y : G), f x = f y →
      ∃! k : G, k ∈ f.ker ∧ y = x * k) ∧
    (∀ (f : G →* H) (x k : G), k ∈ f.ker →
      ∃ y : G, f y = f x ∧ y = x * k) :=
  ⟨same_fiber_inv_mul_mem_ker,
   mul_ker_same_fiber,
   fiber_torsor_unique,
   fiber_torsor_exists⟩

end Omega.CircleDimension
