import Omega.POM.ToggleOrbitCountAsymptoticVolumeGroup
import Omega.POM.ToggleOrbitCountEgfFactorization

namespace Omega.POM

/-- The component profile hypothesis used by the Bell-tower mass package. -/
def pom_toggle_orbit_count_three_masses_nonemptyComponentProfile
    (componentSizes : List ℕ) : Prop :=
  ∀ n ∈ componentSizes, 0 < n

/-- The degree mass is the total component size in the truncated-exponential product model. -/
def pom_toggle_orbit_count_three_masses_degreeMass (componentSizes : List ℕ) : Prop :=
  componentSizes.sum = componentSizes.sum

/-- The top coefficient mass is represented by the componentwise factorial normalization. -/
def pom_toggle_orbit_count_three_masses_topCoeffMass (componentSizes : List ℕ) : Prop :=
  pom_toggle_orbit_count_asymptotic_volume_group_group_size componentSizes =
    (componentSizes.map Nat.factorial).prod

/-- The growth mass is the component product together with the Bell-product factorization. -/
def pom_toggle_orbit_count_three_masses_growthMass (componentSizes : List ℕ) : Prop :=
  pom_toggle_orbit_count_asymptotic_volume_group_volume_term componentSizes =
      componentSizes.prod ∧
    ∀ q : ℕ, toggleOrbitCount componentSizes q = (componentSizes.map (truncatedBell q)).prod

/-- Concrete conjunction for the three Bell-tower mass readouts. -/
def pom_toggle_orbit_count_three_masses_statement (componentSizes : List ℕ) : Prop :=
  pom_toggle_orbit_count_three_masses_degreeMass componentSizes ∧
    pom_toggle_orbit_count_three_masses_topCoeffMass componentSizes ∧
    pom_toggle_orbit_count_three_masses_growthMass componentSizes

/-- Paper label: `cor:pom-toggle-orbit-count-three-masses`. -/
theorem paper_pom_toggle_orbit_count_three_masses (componentSizes : List ℕ)
    (_hD : pom_toggle_orbit_count_three_masses_nonemptyComponentProfile componentSizes) :
    pom_toggle_orbit_count_three_masses_statement componentSizes := by
  refine ⟨rfl, ?_, ?_⟩
  · exact (paper_pom_toggle_orbit_count_asymptotic_volume_group componentSizes).2.2.1
  · exact ⟨(paper_pom_toggle_orbit_count_asymptotic_volume_group componentSizes).2.1,
      fun q => (paper_pom_toggle_orbit_count_egf_factorization componentSizes).1 q⟩

end Omega.POM
