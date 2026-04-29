import Omega.Zeta.DampedPoles

namespace Omega.Zeta

/-- Concrete Abel-Weil pole package for the Hardy criterion at damping parameter `delta`. -/
structure hardy_criterion_delta_data where
  hardy_criterion_delta_base : ℚ
  hardy_criterion_delta_delta : ℕ
  hardy_criterion_delta_pole_count : ℕ
  hardy_criterion_delta_pole_exponent : Fin hardy_criterion_delta_pole_count → ℕ
  hardy_criterion_delta_base_ne_zero : hardy_criterion_delta_base ≠ 0

/-- The Hardy-energy side of the criterion: after damping, every packaged pole has radius
strictly outside the unit disk in the base-radius presentation. -/
def hardy_criterion_delta_hardy_energy_condition
    (D : hardy_criterion_delta_data) : Prop :=
  ∀ i,
    (1 : ℚ) <
      damped_poles_base_radius D.hardy_criterion_delta_base
          (D.hardy_criterion_delta_pole_exponent i) *
        D.hardy_criterion_delta_base ^ D.hardy_criterion_delta_delta

/-- The damped-pole side of the criterion: every pole satisfies the unit-disk holomorphy
criterion after applying the damping parameter. -/
def hardy_criterion_delta_damped_poles_outside_unit_disk
    (D : hardy_criterion_delta_data) : Prop :=
  ∀ i,
    damped_poles_unit_disk_holomorphic_criterion D.hardy_criterion_delta_base
      (D.hardy_criterion_delta_pole_exponent i) D.hardy_criterion_delta_delta

/-- Abstract Abel-Weil Hardy criterion specialized to the concrete damped-poles package. -/
def hardy_criterion_delta_statement (D : hardy_criterion_delta_data) : Prop :=
  hardy_criterion_delta_hardy_energy_condition D ↔
    hardy_criterion_delta_damped_poles_outside_unit_disk D

/-- Paper label: `thm:hardy-criterion-delta`. -/
theorem paper_hardy_criterion_delta
    (D : hardy_criterion_delta_data) : hardy_criterion_delta_statement D := by
  constructor
  · intro hEnergy i
    have hcorr :=
      (paper_damped_poles D.hardy_criterion_delta_base
        (D.hardy_criterion_delta_pole_exponent i) D.hardy_criterion_delta_delta
        D.hardy_criterion_delta_base_ne_zero).2.2
    exact hcorr.mpr (hEnergy i)
  · intro hOutside i
    have hcorr :=
      (paper_damped_poles D.hardy_criterion_delta_base
        (D.hardy_criterion_delta_pole_exponent i) D.hardy_criterion_delta_delta
        D.hardy_criterion_delta_base_ne_zero).2.2
    exact hcorr.mp (hOutside i)

end Omega.Zeta
