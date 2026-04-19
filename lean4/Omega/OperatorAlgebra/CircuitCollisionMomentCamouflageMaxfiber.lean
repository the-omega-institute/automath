import Mathlib.Tactic

namespace Omega.OperatorAlgebra

/-- The verified Prouhet block with positive Thue-Morse sign on `0, ..., 7`. -/
def prouhetLeftProfile : List ℕ :=
  [0, 3, 5, 6]

/-- The complementary Prouhet block with negative Thue-Morse sign on `0, ..., 7`. -/
def prouhetRightProfile : List ℕ :=
  [1, 2, 4, 7]

/-- Power-sum collision proxy attached to a finite fiber-size profile. -/
def profilePowerSum (profile : List ℕ) (q : Nat) : ℕ :=
  (profile.map fun n => n ^ q).sum

/-- Concrete proxy data for the low-order collision camouflage/maxfiber separation package. -/
structure CircuitCollisionCamouflageData (k : Nat) where
  leftProfile : List ℕ
  rightProfile : List ℕ
  lowMaxfiber : ℚ
  highMaxfiber : ℚ
  threshold : ℚ

/-- The two profiles agree on every verified collision moment up to the available Prouhet order. -/
def CircuitCollisionCamouflageData.lowOrderCollisionMomentsMatch
    {k : Nat} (D : CircuitCollisionCamouflageData k) : Prop :=
  D.leftProfile = prouhetLeftProfile ∧
    D.rightProfile = prouhetRightProfile ∧
    ∀ q ≤ Nat.min k 2, profilePowerSum D.leftProfile q = profilePowerSum D.rightProfile q

/-- The maxfiber proxies are separated by the explicit midpoint of the dyadic interval
`(2^k, 2^(k+1))`. -/
def CircuitCollisionCamouflageData.maxfiberThresholdSeparated
    {k : Nat} (D : CircuitCollisionCamouflageData k) : Prop :=
  D.lowMaxfiber = (2 ^ k : ℚ) ∧
    D.highMaxfiber = (2 ^ (k + 1) : ℚ) ∧
    D.threshold = (3 : ℚ) * (2 ^ k : ℚ) / 2 ∧
    D.lowMaxfiber < D.threshold ∧
    D.threshold < D.highMaxfiber

private lemma prouhet_profiles_match (q : Nat) (hq : q ≤ 2) :
    profilePowerSum prouhetLeftProfile q = profilePowerSum prouhetRightProfile q := by
  interval_cases q <;> norm_num [profilePowerSum, prouhetLeftProfile, prouhetRightProfile]

/-- Paper label:
`thm:circuit-prouhet-collision-moment-camouflage-maxfiber`.

The concrete Prouhet partition on eight indices matches the first three power sums, and the dyadic
maxfiber proxies `2^k < 3·2^k/2 < 2^(k+1)` are separated by an explicit threshold. -/
theorem paper_circuit_prouhet_collision_moment_camouflage_maxfiber (k : Nat) (hk : 2 <= k) :
    ∃ D : CircuitCollisionCamouflageData k,
      D.lowOrderCollisionMomentsMatch ∧ D.maxfiberThresholdSeparated := by
  refine ⟨{
    leftProfile := prouhetLeftProfile,
    rightProfile := prouhetRightProfile,
    lowMaxfiber := (2 ^ k : ℚ),
    highMaxfiber := (2 ^ (k + 1) : ℚ),
    threshold := (3 : ℚ) * (2 ^ k : ℚ) / 2
  }, ?_⟩
  constructor
  · refine ⟨rfl, rfl, ?_⟩
    intro q hq
    have hk' : Nat.min k 2 = 2 := Nat.min_eq_right hk
    rw [hk'] at hq
    exact prouhet_profiles_match q hq
  · refine ⟨rfl, rfl, rfl, ?_, ?_⟩
    · have hpowpos : (0 : ℚ) < (2 ^ k : ℚ) := by positivity
      nlinarith
    · have hpowpos : (0 : ℚ) < (2 ^ k : ℚ) := by positivity
      have hpow : (2 ^ (k + 1) : ℚ) = (2 ^ k : ℚ) * 2 := by
        rw [pow_succ]
      nlinarith

end Omega.OperatorAlgebra
