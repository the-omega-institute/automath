import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.POM.ToggleOrbitCountBellProduct

namespace Omega.POM

/-- The componentwise volume term appearing in the Bell-product orbit-count expansion. -/
def pom_toggle_orbit_count_asymptotic_volume_group_volume_term
    (componentSizes : List ℕ) : ℕ :=
  componentSizes.prod

/-- The componentwise permutation-group normalization. -/
def pom_toggle_orbit_count_asymptotic_volume_group_group_size
    (componentSizes : List ℕ) : ℕ :=
  (componentSizes.map Nat.factorial).prod

/-- The exact normalized orbit count obtained by multiplying with the componentwise group size. -/
def pom_toggle_orbit_count_asymptotic_volume_group_normalized
    (componentSizes : List ℕ) (q : ℕ) : ℕ :=
  pom_toggle_orbit_count_asymptotic_volume_group_group_size componentSizes *
    toggleOrbitCount componentSizes q

/-- The logarithmic volume proxy used by the paper-facing wrapper. -/
noncomputable def pom_toggle_orbit_count_asymptotic_volume_group_log_volume
    (componentSizes : List ℕ) : ℝ :=
  Real.log (pom_toggle_orbit_count_asymptotic_volume_group_volume_term componentSizes)

/-- Concrete Bell-product package exposing the component product, the volume term, the group-size
normalization, and its exact factorization. -/
def PomToggleOrbitCountAsymptoticVolumeGroup (componentSizes : List ℕ) : Prop :=
  (∀ q : ℕ,
    toggleOrbitCount componentSizes q = (componentSizes.map (truncatedBell q)).prod) ∧
    pom_toggle_orbit_count_asymptotic_volume_group_volume_term componentSizes =
      componentSizes.prod ∧
    pom_toggle_orbit_count_asymptotic_volume_group_group_size componentSizes =
      (componentSizes.map Nat.factorial).prod ∧
    (∀ q : ℕ,
      pom_toggle_orbit_count_asymptotic_volume_group_normalized componentSizes q =
        (componentSizes.map (fun n => Nat.factorial n * truncatedBell q n)).prod) ∧
    pom_toggle_orbit_count_asymptotic_volume_group_log_volume componentSizes =
      Real.log (componentSizes.prod)

/-- Paper label: `thm:pom-toggle-orbit-count-asymptotic-volume-group`. -/
theorem paper_pom_toggle_orbit_count_asymptotic_volume_group
    (componentSizes : List ℕ) : PomToggleOrbitCountAsymptoticVolumeGroup componentSizes := by
  refine ⟨(fun q => paper_pom_toggle_orbit_count_bell_product q componentSizes), rfl, rfl, ?_, rfl⟩
  intro q
  induction componentSizes with
  | nil =>
      simp [pom_toggle_orbit_count_asymptotic_volume_group_normalized,
        pom_toggle_orbit_count_asymptotic_volume_group_group_size, toggleOrbitCount]
  | cons n ns ih =>
      calc
        pom_toggle_orbit_count_asymptotic_volume_group_normalized (n :: ns) q
            = (n.factorial * truncatedBell q n) *
                pom_toggle_orbit_count_asymptotic_volume_group_normalized ns q := by
              simp [pom_toggle_orbit_count_asymptotic_volume_group_normalized,
                pom_toggle_orbit_count_asymptotic_volume_group_group_size, toggleOrbitCount,
                Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
        _ = (n.factorial * truncatedBell q n) *
              (ns.map (fun n => Nat.factorial n * truncatedBell q n)).prod := by
              rw [ih]
        _ = ((n :: ns).map (fun n => Nat.factorial n * truncatedBell q n)).prod := by
              simp

end Omega.POM
