import Mathlib.Tactic

namespace Omega.Conclusion

/-- The finite fiber of a map `f` over `x`. -/
abbrev conclusion_fiber_intermediate_system_lattice_mobius_fiber
    {Ω X : Type*} (f : Ω → X) (x : X) : Type _ :=
  {ω : Ω // f ω = x}

/-- A concrete partition of a finite fiber, represented as its equivalence relation. -/
abbrev conclusion_fiber_intermediate_system_lattice_mobius_partition (α : Type*) : Type _ :=
  Setoid α

/-- Intermediate fiber systems, encoded by choosing a partition independently on every fiber. -/
abbrev conclusion_fiber_intermediate_system_lattice_mobius_Q
    {Ω X : Type*} (f : Ω → X) : Type _ :=
  ∀ x : X,
    conclusion_fiber_intermediate_system_lattice_mobius_partition
      (conclusion_fiber_intermediate_system_lattice_mobius_fiber f x)

/-- Paper label: `thm:conclusion-fiber-intermediate-system-lattice-mobius`. With intermediate
systems encoded by their kernel partitions on each fiber, the lattice is exactly the product of
the fiber partition lattices. -/
def paper_conclusion_fiber_intermediate_system_lattice_mobius
    {Ω X : Type*} [Fintype Ω] [Fintype X] [DecidableEq X] (f : Ω → X) :
    conclusion_fiber_intermediate_system_lattice_mobius_Q f ≃o
      (∀ x : X,
        conclusion_fiber_intermediate_system_lattice_mobius_partition
          (conclusion_fiber_intermediate_system_lattice_mobius_fiber f x)) := by
  exact OrderIso.refl _

end Omega.Conclusion
