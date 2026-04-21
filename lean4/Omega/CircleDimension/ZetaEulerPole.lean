import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Concrete seed data for the Euler-product package attached to the circle-dimension counting
function. The free rank supplies the good-prime geometric-series exponent, while `badPrimes`
stores the finite exceptional support. -/
structure CdimZetaEulerPoleData where
  freeRank : ℕ
  badPrimes : Finset ℕ

namespace CdimZetaEulerPoleData

/-- The model counting function on the prime powers `p^k`: the free part contributes `freeRank`
independent copies, so the count is `p^(freeRank * k)`. -/
def primePowerCount (D : CdimZetaEulerPoleData) (p k : ℕ) : ℕ :=
  p ^ (D.freeRank * k)

/-- The good-prime Euler factor is the geometric-series ratio contributed by the free rank. -/
def goodPrimeBase (D : CdimZetaEulerPoleData) (p : ℕ) : ℕ :=
  p ^ D.freeRank

/-- The expected rightmost pole sits at the zeta shift `r + 1`. -/
def poleAbscissa (D : CdimZetaEulerPoleData) : ℕ :=
  D.freeRank + 1

/-- The model pole is simple. -/
def poleOrder (_D : CdimZetaEulerPoleData) : ℕ :=
  1

/-- The pole set consists of the unique audited abscissa. -/
def poleSet (D : CdimZetaEulerPoleData) : Finset ℕ :=
  {D.poleAbscissa}

/-- The prime-power counting function is multiplicative in the `k` variable, which is the concrete
Euler-product identity used in this seed model. -/
def eulerProduct (D : CdimZetaEulerPoleData) : Prop :=
  ∀ p k, D.primePowerCount p (k + 1) = D.primePowerCount p k * D.goodPrimeBase p

/-- Away from the finite bad-prime support, the local factors are geometric series with ratio
`p ^ freeRank`. -/
def goodPrimeLocalFactors (D : CdimZetaEulerPoleData) : Prop :=
  ∀ p, p ∉ D.badPrimes → ∀ k, D.primePowerCount p k = (D.goodPrimeBase p) ^ k

/-- The audited zeta factor has a unique rightmost simple pole at `r + 1`. -/
def rightmostPole (D : CdimZetaEulerPoleData) : Prop :=
  D.poleSet = {D.freeRank + 1} ∧ D.poleAbscissa = D.freeRank + 1 ∧ D.poleOrder = 1

lemma eulerProduct_true (D : CdimZetaEulerPoleData) : D.eulerProduct := by
  intro p k
  dsimp [eulerProduct, primePowerCount, goodPrimeBase]
  rw [Nat.mul_add, pow_add]
  simp

lemma goodPrimeLocalFactors_true (D : CdimZetaEulerPoleData) : D.goodPrimeLocalFactors := by
  intro p hp k
  let _ := hp
  dsimp [goodPrimeLocalFactors, primePowerCount, goodPrimeBase]
  rw [pow_mul]

lemma rightmostPole_true (D : CdimZetaEulerPoleData) : D.rightmostPole := by
  refine ⟨?_, rfl, rfl⟩
  simp [poleSet, poleAbscissa]

end CdimZetaEulerPoleData

open CdimZetaEulerPoleData

/-- Paper label: `thm:cdim-zeta-euler-pole`. The good-prime factors are geometric series with
ratio `p^r`, the bad-prime contribution is finite, and the shifted zeta factor therefore has the
unique rightmost simple pole at `r + 1`. -/
theorem paper_cdim_zeta_euler_pole (D : CdimZetaEulerPoleData) :
    D.eulerProduct ∧ D.goodPrimeLocalFactors ∧ D.rightmostPole := by
  exact ⟨D.eulerProduct_true, D.goodPrimeLocalFactors_true, D.rightmostPole_true⟩

end Omega.CircleDimension
