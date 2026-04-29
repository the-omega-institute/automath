import Mathlib.Tactic
import Omega.CircleDimension.KilloS4BurnsideKaniRosenPrymSquare
import Omega.CircleDimension.S4EvenSubgroupFreeActionUnramifiedA4Lift

namespace Omega.CircleDimension

/-- Concrete bookkeeping package for the two Prym polarization types appearing in the
`S₄/A₄/V₄` Hurwitz tower. The `C₆/H` side is supplied by the audited unramified `A₄`-lift, while
the `Y/Z` side records the double-cover Hurwitz data used for the branched Prym formula. -/
structure killo_two_prym_polarization_types_data where
  liftData : killo_s4_even_subgroup_free_action_unramified_a4_lift_data
  yzCoverGenus : ℕ
  yzBaseGenus : ℕ
  yzRamificationPairs : ℕ
  yzCoverGenus_eq : yzCoverGenus = 13
  yzBaseGenus_eq : yzBaseGenus = 4
  yzHurwitz : yzCoverGenus = 2 * yzBaseGenus - 1 + yzRamificationPairs

namespace killo_two_prym_polarization_types_data

/-- For an unramified cyclic triple cover `C₆ → H`, the Prym polarization type is
`(1^(g(H)-1), 3^(g(H)-1))`. -/
def prymC6HPolarization (D : killo_two_prym_polarization_types_data) : List ℕ :=
  List.replicate (D.liftData.genusH - 1) 1 ++ List.replicate (D.liftData.genusH - 1) 3

/-- The cyclic triple-cover deck action together with the `A₂` determinant witness packages the
chapter-local Eisenstein endomorphism certificate. -/
def prymC6HEisensteinEndomorphisms (D : killo_two_prym_polarization_types_data) : Prop :=
  D.liftData.c6ToHIsCyclicTripleCover ∧ a2CartanForm.det = 3

/-- For a branched double cover `Y → Z` with `g(Z) = 4` and six ramification pairs, the Prym
polarization type is `(1^g(Z), 2^(r-1))`. -/
def prymYZPolarization (D : killo_two_prym_polarization_types_data) : List ℕ :=
  List.replicate D.yzBaseGenus 1 ++ List.replicate (D.yzRamificationPairs - 1) 2

end killo_two_prym_polarization_types_data

open killo_two_prym_polarization_types_data

/-- Paper label: `prop:killo-two-prym-polarization-types`. -/
theorem paper_killo_two_prym_polarization_types (D : killo_two_prym_polarization_types_data) :
    D.prymC6HPolarization = [1, 1, 1, 1, 3, 3, 3, 3] ∧ D.prymC6HEisensteinEndomorphisms ∧
      D.prymYZPolarization = [1, 1, 1, 1, 2, 2, 2, 2, 2] := by
  have hLift := paper_killo_s4_even_subgroup_free_action_unramified_a4_lift D.liftData
  have hGenusH : D.liftData.genusH = 5 := hLift.2.2.1
  have hTriple : D.liftData.c6ToHIsCyclicTripleCover := hLift.2.2.2.2.1
  have hA2Det : a2CartanForm.det = 3 := by
    rcases paper_killo_s4_burnside_kani_rosen_prym_square with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, hdet, _⟩
    exact hdet
  have hRamificationPairs : D.yzRamificationPairs = 6 := by
    have hHurwitz := D.yzHurwitz
    rw [D.yzCoverGenus_eq, D.yzBaseGenus_eq] at hHurwitz
    omega
  refine ⟨?_, ?_, ?_⟩
  · simp [killo_two_prym_polarization_types_data.prymC6HPolarization, hGenusH]
  · exact ⟨hTriple, hA2Det⟩
  · simp [killo_two_prym_polarization_types_data.prymYZPolarization, D.yzBaseGenus_eq,
      hRamificationPairs]

end Omega.CircleDimension
