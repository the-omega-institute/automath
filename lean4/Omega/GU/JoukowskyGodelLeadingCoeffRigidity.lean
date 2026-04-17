import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace Omega.GU

open scoped BigOperators

/-- Concrete transport data for the Joukowsky--Godel leading-coefficient identity. The
`hVieta` field packages the Vieta relation
`a_n * ((-1)^n * ∏ z_j) = a_0`. -/
structure JoukowskyGodelTransportData (K : Type*) [Field K] where
  n : Nat
  a_n : K
  a_0 : K
  r : K
  roots : Fin n → K
  hVieta : a_n * (((-1 : K) ^ n) * ∏ j : Fin n, roots j) = a_0

/-- The product of the linear `w`-coefficients in the transport factorization. -/
def JoukowskyGodelTransportData.transportLeadingCoeff {K : Type*} [Field K]
    (D : JoukowskyGodelTransportData K) : K :=
  D.a_n ^ 2 * (((-1 : K) ^ D.n) * ∏ j : Fin D.n, D.roots j)

/-- The leading coefficient is rigid and equals `a_n a_0`. -/
def JoukowskyGodelTransportData.leadingCoeffRigidity {K : Type*} [Field K]
    (D : JoukowskyGodelTransportData K) : Prop :=
  D.transportLeadingCoeff = D.a_n * D.a_0

/-- `thm:group-jg-lc-rigidity` -/
theorem paper_group_jg_lc_rigidity {K : Type*} [Field K] (D : JoukowskyGodelTransportData K) :
    D.leadingCoeffRigidity := by
  dsimp [JoukowskyGodelTransportData.leadingCoeffRigidity,
    JoukowskyGodelTransportData.transportLeadingCoeff]
  calc
    D.a_n ^ 2 * (((-1 : K) ^ D.n) * ∏ j : Fin D.n, D.roots j)
        = D.a_n * (D.a_n * (((-1 : K) ^ D.n) * ∏ j : Fin D.n, D.roots j)) := by
            simp [pow_two, mul_assoc, mul_left_comm, mul_comm]
    _ = D.a_n * D.a_0 := by rw [D.hVieta]

end Omega.GU
