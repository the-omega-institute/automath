import Mathlib.Tactic
import Omega.Zeta.CyclicPTypicalFrobeniusVerschiebung

namespace Omega.Conclusion

open Omega.Zeta

/-- The concrete `TC₁` seed model for the real-input-40 length-two primitive atom. -/
def conclusion_realinput40_two_typical_ghost_irreducibility_model_block (u : ℤ) :
    CyclicPBlock :=
  { exponent := 1, scalar := u }

/-- A chosen `2`-typical Verschiebung lift for the length-two atom. -/
def conclusion_realinput40_two_typical_ghost_irreducibility_rooted_model
    (u liftScalar : ℤ) (hlift : liftScalar ^ 2 = u) : RootedCyclicPBlock 2 :=
  { base := { exponent := 0, scalar := u }, liftScalar := liftScalar, lift_spec := hlift }

/-- The `2`-typical ghost tower of the concrete length-two atom is read from the `2^n` trace
coordinates. -/
def conclusion_realinput40_two_typical_ghost_irreducibility_two_typical_ghost_tower
    (u : ℤ) (n : ℕ) : ℤ :=
  directSumTrace 2 [conclusion_realinput40_two_typical_ghost_irreducibility_model_block u] (2 ^ n)

/-- A shorter primitive profile has no support at length `2` or above. -/
def conclusion_realinput40_two_typical_ghost_irreducibility_short_support
    (ghost : ℕ → ℤ) : Prop :=
  ∀ n, 2 ≤ n → ghost n = 0

/-- Paper label: `thm:conclusion-realinput40-two-typical-ghost-irreducibility`.
The length-two real-input-40 atom has an explicit `2`-typical ghost tower, satisfies the
Frobenius--Verschiebung law at `p = 2`, and cannot be reproduced by a profile supported only in
lengths `< 2`. -/
theorem paper_conclusion_realinput40_two_typical_ghost_irreducibility
    (u liftScalar : ℤ) (hu : u ≠ 0) (hlift : liftScalar ^ 2 = u) (shortGhost : ℕ → ℤ)
    (hshort :
      conclusion_realinput40_two_typical_ghost_irreducibility_short_support shortGhost) :
    (∀ n : ℕ,
      conclusion_realinput40_two_typical_ghost_irreducibility_two_typical_ghost_tower u n =
        directSumTrace 2 [conclusion_realinput40_two_typical_ghost_irreducibility_model_block u]
          (2 ^ n)) ∧
      frobeniusSum 2
          (verschiebungSum
            [conclusion_realinput40_two_typical_ghost_irreducibility_rooted_model u liftScalar
              hlift]) =
        baseReplicateSum 2
          [conclusion_realinput40_two_typical_ghost_irreducibility_rooted_model u liftScalar
            hlift] ∧
      ¬ ∀ n : ℕ,
        shortGhost (2 ^ n) =
          conclusion_realinput40_two_typical_ghost_irreducibility_two_typical_ghost_tower u n := by
  refine ⟨fun n => rfl, ?_, ?_⟩
  · simpa using
      (paper_cyclic_p_typical_frobenius_verschiebung
        2 (by decide)
        []
        [conclusion_realinput40_two_typical_ghost_irreducibility_rooted_model u liftScalar
          hlift]).2
  · intro hmatch
    have hzero : shortGhost 2 = 0 := hshort 2 (by norm_num)
    have hvalue :
        shortGhost 2 =
          conclusion_realinput40_two_typical_ghost_irreducibility_two_typical_ghost_tower u 1 := by
      simpa using hmatch 1
    have hghost :
        conclusion_realinput40_two_typical_ghost_irreducibility_two_typical_ghost_tower u 1 =
          2 * u ^ 2 := by
      simp [conclusion_realinput40_two_typical_ghost_irreducibility_two_typical_ghost_tower,
        conclusion_realinput40_two_typical_ghost_irreducibility_model_block, directSumTrace,
        blockTracePower, blockLength]
    have hnonzero : (2 : ℤ) * u ^ 2 ≠ 0 := by
      exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hu)
    have hcontr : (2 : ℤ) * u ^ 2 = 0 := by
      calc
        (2 : ℤ) * u ^ 2 =
            conclusion_realinput40_two_typical_ghost_irreducibility_two_typical_ghost_tower u 1 := by
              simpa [hghost]
        _ = shortGhost 2 := by simpa using hvalue.symm
        _ = 0 := hzero
    exact hnonzero hcontr

end Omega.Conclusion
