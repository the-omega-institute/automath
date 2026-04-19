import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Omega.GU.Window6CyclicWeightThresholdRootLength

namespace Omega.GU

/-- The five `C₆`-orbits appearing in the window-`6` root-sector analysis. -/
abbrev Window6C6Orbit := Fin 5

/-- A concrete universe of orbit points used to package the orbit decomposition as finite sets. -/
abbrev Window6OrbitPoint := Fin 30

/-- Concrete data for the `C₆`-orbit versus `B₃` root-sector rigidity statement. -/
structure Window6C6OrbitB3RootIntersectionRigidityData where
  orbits : Window6C6Orbit → Finset Window6OrbitPoint
  orbitCardSix : ∀ i, (orbits i).card = 6
  weight : Window6C6Orbit → ℕ
  shortOrbit : Window6C6Orbit
  longOrbitWitness : Window6C6Orbit
  short_ne_long : shortOrbit ≠ longOrbitWitness
  shortWeight : weight shortOrbit = 1
  longWeights : ∀ i, i ≠ shortOrbit → weight i = 2

/-- The unique short-root sector. -/
def Window6C6OrbitB3RootIntersectionRigidityData.shortRootSector
    (D : Window6C6OrbitB3RootIntersectionRigidityData) : Finset Window6C6Orbit :=
  {D.shortOrbit}

/-- The complementary long-root sector. -/
def Window6C6OrbitB3RootIntersectionRigidityData.longRootSector
    (D : Window6C6OrbitB3RootIntersectionRigidityData) : Finset Window6C6Orbit :=
  Finset.univ.erase D.shortOrbit

/-- Exactly one orbit has weight `1`, hence exactly one orbit meets the short-root sector. -/
def Window6C6OrbitB3RootIntersectionRigidityData.uniqueShortOrbit
    (D : Window6C6OrbitB3RootIntersectionRigidityData) : Prop :=
  ∀ i, D.weight i = 1 ↔ i = D.shortOrbit

/-- Every other orbit lies in the long-root sector, detected here by weight `2`. -/
def Window6C6OrbitB3RootIntersectionRigidityData.remainingOrbitsLong
    (D : Window6C6OrbitB3RootIntersectionRigidityData) : Prop :=
  ∀ i, i ≠ D.shortOrbit → D.weight i = 2

/-- Short-root indicator on the orbit set. -/
def Window6C6OrbitB3RootIntersectionRigidityData.shortIndicator
    (D : Window6C6OrbitB3RootIntersectionRigidityData) : Window6C6Orbit → ℚ :=
  fun i => if i = D.shortOrbit then 1 else 0

/-- Long-root indicator on the orbit set. -/
def Window6C6OrbitB3RootIntersectionRigidityData.longIndicator
    (D : Window6C6OrbitB3RootIntersectionRigidityData) : Window6C6Orbit → ℚ :=
  fun i => if i = D.shortOrbit then 0 else 1

/-- Orbit-constant Weyl-invariant functions are exactly the functions constant on the short and
long sectors. -/
def Window6C6OrbitB3RootIntersectionRigidityData.orbitConstantOnSectors
    (D : Window6C6OrbitB3RootIntersectionRigidityData) (f : Window6C6Orbit → ℚ) : Prop :=
  (∀ i, i = D.shortOrbit → f i = f D.shortOrbit) ∧
    ∀ i, i ≠ D.shortOrbit → f i = f D.longOrbitWitness

/-- The space of Weyl-invariant orbit-constant functions is spanned by the short- and long-sector
indicators, so it is effectively two-dimensional. -/
def Window6C6OrbitB3RootIntersectionRigidityData.orbitConstantWeylInvariantDimTwo
    (D : Window6C6OrbitB3RootIntersectionRigidityData) : Prop :=
  ∀ f : Window6C6Orbit → ℚ,
    D.orbitConstantOnSectors f →
    ∃ a b : ℚ, ∀ i, f i = a * D.shortIndicator i + b * D.longIndicator i

/-- Among the five `C₆`-orbits, the unique weight-`1` orbit is the short-root orbit, all others
have long-root weight `2`, and any Weyl-invariant orbit-constant function is determined by its
short- and long-sector values.
    thm:window6-c6-orbit-b3-root-intersection-rigidity -/
theorem paper_window6_c6_orbit_b3_root_intersection_rigidity
    (D : Window6C6OrbitB3RootIntersectionRigidityData) :
    D.uniqueShortOrbit ∧ D.remainingOrbitsLong ∧ D.orbitConstantWeylInvariantDimTwo := by
  have hThreshold :=
    paper_window6_cyclic_weight_threshold_root_length
      (weightOneShortRootOrbit := D.weight D.shortOrbit = 1)
      (nonWeightOneLongRootOrbit := D.remainingOrbitsLong)
      (weylOrbitPartition := D.uniqueShortOrbit)
      D.shortWeight D.longWeights (by
        intro h
        rcases h with ⟨hShort, hLong⟩
        intro i
        constructor
        · intro hi
          by_cases his : i = D.shortOrbit
          · exact his
          · have hTwo : D.weight i = 2 := hLong i his
            omega
        · intro hi
          simpa [hi] using hShort)
  refine ⟨hThreshold.2.2, hThreshold.2.1, ?_⟩
  intro f hf
  refine ⟨f D.shortOrbit, f D.longOrbitWitness, ?_⟩
  intro i
  by_cases hi : i = D.shortOrbit
  · subst hi
    simp [Window6C6OrbitB3RootIntersectionRigidityData.shortIndicator,
      Window6C6OrbitB3RootIntersectionRigidityData.longIndicator]
  · have hLongValue : f i = f D.longOrbitWitness := hf.2 i hi
    simp [Window6C6OrbitB3RootIntersectionRigidityData.shortIndicator,
      Window6C6OrbitB3RootIntersectionRigidityData.longIndicator, hi, hLongValue]

end Omega.GU
