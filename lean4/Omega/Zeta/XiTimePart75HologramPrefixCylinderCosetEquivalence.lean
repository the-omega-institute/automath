import Mathlib.Tactic

namespace Omega.Zeta

universe u v

/-- Concrete data for the prefix-cylinder/coset comparison.  A prefix cylinder in the address
space is mapped to a target coset, with image equality and prefix separation supplying the
finite-address injectivity needed for the induced bijection. -/
structure xi_time_part75_hologram_prefix_cylinder_coset_equivalence_data where
  Prefix : Type u
  Address : Type v
  addressMap : Prefix → Address
  prefixCylinder : Set Prefix
  targetCoset : Set Address
  prefixCylinder_image_eq_targetCoset :
    Set.image addressMap prefixCylinder = targetCoset
  prefixCylinder_separated :
    Set.InjOn addressMap prefixCylinder

/-- The induced map from the prefix cylinder to the target coset. -/
def xi_time_part75_hologram_prefix_cylinder_coset_equivalence_prefix_to_coset
    (D : xi_time_part75_hologram_prefix_cylinder_coset_equivalence_data) :
    D.prefixCylinder → D.targetCoset :=
  fun x =>
    ⟨D.addressMap x.1, by
      rw [← D.prefixCylinder_image_eq_targetCoset]
      exact ⟨x.1, x.2, rfl⟩⟩

/-- The prefix-cylinder image is exactly the audited target coset. -/
def xi_time_part75_hologram_prefix_cylinder_coset_equivalence_data.prefix_image_coset_identity
    (D : xi_time_part75_hologram_prefix_cylinder_coset_equivalence_data) : Prop :=
  Set.image D.addressMap D.prefixCylinder = D.targetCoset

/-- The audited address map induces a bijection between the prefix cylinder and the target coset. -/
def xi_time_part75_hologram_prefix_cylinder_coset_equivalence_data.prefix_coset_bijection
    (D : xi_time_part75_hologram_prefix_cylinder_coset_equivalence_data) : Prop :=
  Function.Bijective
    (xi_time_part75_hologram_prefix_cylinder_coset_equivalence_prefix_to_coset D)

/-- Paper label: `thm:xi-time-part75-hologram-prefix-cylinder-coset-equivalence`.  The audited
image identity identifies the prefix cylinder with the coset image, while prefix separation makes
the induced address map injective and the image identity makes it surjective. -/
theorem paper_xi_time_part75_hologram_prefix_cylinder_coset_equivalence
    (D : xi_time_part75_hologram_prefix_cylinder_coset_equivalence_data) :
    D.prefix_image_coset_identity ∧ D.prefix_coset_bijection := by
  refine ⟨D.prefixCylinder_image_eq_targetCoset, ?_⟩
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply D.prefixCylinder_separated x.2 y.2
    exact congrArg Subtype.val hxy
  · intro y
    have hy : y.1 ∈ Set.image D.addressMap D.prefixCylinder := by
      rw [D.prefixCylinder_image_eq_targetCoset]
      exact y.2
    rcases hy with ⟨x, hx, hxy⟩
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

end Omega.Zeta
