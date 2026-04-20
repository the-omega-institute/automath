import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.POM.CoprimeLedgerPrimorialOptimality

namespace Omega.GroupUnification

/-- The chapter-local ellipsoid-volume formula as a monotone function of the total Gödel cost. -/
noncomputable def godelEllipsoidVolume (M : ℕ) (N : ℕ) : ℝ :=
  (M : ℝ) * Real.log N

/-- The corresponding Joukowsky-area formula, transported from the same logarithmic cost. -/
noncomputable def godelJoukowskyArea (M : ℕ) (N : ℕ) : ℝ :=
  2 * godelEllipsoidVolume M N

/-- For pairwise coprime ledger bases, the chosen prime divisors are distinct; the existing
primorial comparison therefore bounds the total Gödel cost below by the first-prime product, and
monotonicity transports the same lower bound to the ellipsoid-volume and Joukowsky-area formulas.
    prop:group-jg-min-total-godel-cost-primorial -/
theorem paper_group_jg_min_total_godel_cost_primorial
    (T M : ℕ) (q : Fin T → ℕ)
    (hq : ∀ i, 2 ≤ q i)
    (hpair : Pairwise fun i j => Nat.Coprime (q i) (q j)) :
    godelEllipsoidVolume M (Omega.POM.firstPrimeProduct T) ≤
        godelEllipsoidVolume M (Omega.POM.ledgerProduct q) ∧
      Omega.POM.firstPrimeProduct T ≤ Omega.POM.ledgerProduct q ∧
      godelJoukowskyArea M (Omega.POM.firstPrimeProduct T) ≤
        godelJoukowskyArea M (Omega.POM.ledgerProduct q) := by
  rcases Omega.POM.paper_pom_coprime_ledger_primorial_optimality T M q hq hpair with
    ⟨hEllipsoid, hPrimorial, _⟩
  refine ⟨hEllipsoid, hPrimorial, ?_⟩
  unfold godelJoukowskyArea
  exact mul_le_mul_of_nonneg_left hEllipsoid (by positivity)

end Omega.GroupUnification
