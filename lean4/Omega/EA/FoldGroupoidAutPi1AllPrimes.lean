import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic
import Omega.EA.FoldGroupoidAut0RationalCohomology
import Omega.Folding.FiberWeightCount

namespace Omega.EA

open scoped BigOperators

/-- Finite-product order proxy for the connected fold-groupoid automorphism fundamental group:
the `PU(d)` factors contribute cyclic `π₁` blocks of orders `d = fiberMultiplicity x`, so the
product of the block orders is modeled by the product of the fiber multiplicities. -/
noncomputable def foldGroupoidAutPi1OrderProxy (m : ℕ) : ℕ :=
  ∏ x : X m, X.fiberMultiplicity x

lemma prime_dvd_foldGroupoidAutPi1OrderProxy_of_dvd_factor {m p : ℕ} (x : X m)
    (hp : p ∣ X.fiberMultiplicity x) : p ∣ foldGroupoidAutPi1OrderProxy m := by
  unfold foldGroupoidAutPi1OrderProxy
  exact hp.trans <| by
    simpa using
      (Finset.dvd_prod_of_mem (fun y : X m => X.fiberMultiplicity y) (by simp : x ∈ Finset.univ))

lemma allFalse_fiberMultiplicity_eq_prime (p : ℕ) (hp : Nat.Prime p) :
    X.fiberMultiplicity (⟨fun _ => false, no11_allFalse⟩ : X (2 * (p - 1))) = p := by
  rw [Omega.fiberMultiplicity_allFalse_closed]
  have hp2 : 2 ≤ p := hp.two_le
  omega

/-- Paper label: `prop:fold-groupoid-aut-pi1-all-primes`. The finite-product `PU(d)` proxy has the
expected generator count, and every prime occurs in the order proxy of some connected
fold-groupoid automorphism product because the all-false fiber realizes multiplicity `p` at
resolution `2(p-1)`. -/
theorem paper_fold_groupoid_aut_pi1_all_primes :
    (∀ m : ℕ,
      Fintype.card (foldGroupoidAut0OddGenerator m) = ∑ x : X m, (X.fiberMultiplicity x - 1)) ∧
      (∀ p : ℕ, Nat.Prime p → ∃ m : ℕ, p ∣ foldGroupoidAutPi1OrderProxy m) := by
  refine ⟨?_, ?_⟩
  · intro m
    exact (paper_fold_groupoid_aut0_rational_cohomology m).2.1
  · intro p hp
    refine ⟨2 * (p - 1), ?_⟩
    have hmult :
        X.fiberMultiplicity (⟨fun _ => false, no11_allFalse⟩ : X (2 * (p - 1))) = p :=
      allFalse_fiberMultiplicity_eq_prime p hp
    apply prime_dvd_foldGroupoidAutPi1OrderProxy_of_dvd_factor
    exact dvd_of_eq hmult.symm

end Omega.EA
