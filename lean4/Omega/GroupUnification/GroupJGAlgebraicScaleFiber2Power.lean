import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic

namespace Omega.GroupUnification

/-- Product of the quadratic branching degrees contributed by adjoining the transported roots. -/
def groupJGQuadraticFiberDegree (levels : List ℕ) : ℕ :=
  levels.prod

private lemma groupJGQuadraticFiberDegree_dvd_two_pow :
    ∀ levels : List ℕ, (∀ m ∈ levels, m ∣ 2) →
      groupJGQuadraticFiberDegree levels ∣ 2 ^ levels.length
  | [], _ => by
      simp [groupJGQuadraticFiberDegree]
  | a :: as, hlevels => by
      have ha : a ∣ 2 := hlevels a (by simp)
      have htail : groupJGQuadraticFiberDegree as ∣ 2 ^ as.length :=
        groupJGQuadraticFiberDegree_dvd_two_pow as (by
          intro m hm
          exact hlevels m (by simp [hm]))
      have hmul : a * groupJGQuadraticFiberDegree as ∣ 2 * 2 ^ as.length :=
        Nat.mul_dvd_mul ha htail
      simpa [groupJGQuadraticFiberDegree, Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm,
        Nat.mul_comm] using hmul

/-- Paper label: `prop:group-jg-algebraic-scale-fiber-2power`.
If each transported root lies in an extension of degree dividing `2`, then adjoining `n` such
roots produces a tower whose total degree divides `2^n`. -/
theorem paper_group_jg_algebraic_scale_fiber_2power (n : Nat) :
    ∀ levels : List ℕ, levels.length = n → (∀ m ∈ levels, m ∣ 2) →
      groupJGQuadraticFiberDegree levels ∣ 2 ^ n := by
  intro levels hlen hlevels
  simpa [hlen] using groupJGQuadraticFiberDegree_dvd_two_pow levels hlevels

end Omega.GroupUnification
