import Mathlib.Tactic
import Omega.Folding.CollisionZetaOperator
import Omega.POM.CollisionKernelDiscriminant
import Omega.POM.S5GaloisArithmetic

namespace Omega.POM

open Omega
open Omega.POM.CollisionKernelDiscriminant
open Omega.POM.S5GaloisArithmetic

/-- Concrete residue/conjugacy seed package for the A₂/A₃/A₄ collision-kernel zeta discussion:
the cubic discriminants certify simple poles in the low-rank models, the A₄ Perron pole is
localized in `(3, 4)`, and the nonsquare quintic discriminant provides the Galois-conjugacy
obstruction used in the A₄ residue-family statement. -/
def pomZetaResidueConstantsConjugatesClaim : Prop :=
  cubicDisc (-2) (-2) 2 = 148 ∧
    cubicDisc (-2) (-4) 2 = 564 ∧
    0 < cubicDisc (-2) (-2) 2 ∧
    0 < cubicDisc (-2) (-4) 2 ∧
    collisionKernel4.trace = 2 ∧
    collisionKernel4.det = (-2 : ℤ) ∧
    ((3 : ℤ) ^ 5 - 2 * 3 ^ 4 - 7 * 3 ^ 3 - 2 * 3 + 2 = -112) ∧
    ((4 : ℤ) ^ 5 - 2 * 4 ^ 4 - 7 * 4 ^ 3 - 2 * 4 + 2 = 58) ∧
    2 ^ 4 * 3 ^ 4 * 5 * 11 * 13 * 17383 = (16107783120 : ℕ) ∧
    -(16107783120 : ℤ) < 0 ∧
    ¬ ∃ k : ℤ, k * k = -(16107783120 : ℤ)

/-- Paper label: `prop:pom-zeta-residue-constants-conjugates`. The existing discriminant,
trace/determinant, Perron-pole localization, and quintic Galois arithmetic certificates assemble
the concrete residue-constant/conjugacy seed package used in the paper discussion. -/
theorem paper_pom_zeta_residue_constants_conjugates :
    pomZetaResidueConstantsConjugatesClaim := by
  rcases collision_kernel_universal_invariants with ⟨_, _, _, _, htr4, hdet4⟩
  rcases perron_root_A4_in_interval with ⟨h3, h4⟩
  exact ⟨disc_charPolyA2, disc_charPolyA3, disc_charPolyA2_pos, disc_charPolyA3_pos,
    htr4, hdet4, h3, h4, disc_factorization, disc_negative, disc_not_square⟩

end Omega.POM
