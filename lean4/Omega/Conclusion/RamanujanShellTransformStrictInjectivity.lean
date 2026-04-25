import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Conclusion

/-- A coefficientwise shell transform: on the shell of length `Q`, the sample at residue `n % Q`
selects the matching coefficient and kills the rest. -/
def conclusion_ramanujan_shell_transform_strict_injectivity_shell_transform
    (a : ℕ → ℕ → ℤ) (ℓ Q n : ℕ) : ℤ :=
  Finset.sum (Finset.range Q) fun r => if r = n % Q then a ℓ r else 0

lemma conclusion_ramanujan_shell_transform_strict_injectivity_shell_transform_recovers
    (a : ℕ → ℕ → ℤ) (ℓ r : ℕ) :
    conclusion_ramanujan_shell_transform_strict_injectivity_shell_transform a ℓ (r + 1) r =
      a ℓ r := by
  unfold conclusion_ramanujan_shell_transform_strict_injectivity_shell_transform
  rw [Finset.sum_range_succ]
  have hvanish :
      Finset.sum (Finset.range r) (fun x => if x = r % (r + 1) then a ℓ x else 0) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro x hx
    have hxne : x ≠ r := Nat.ne_of_lt (Finset.mem_range.mp hx)
    simp [Nat.mod_eq_of_lt (Nat.lt_succ_self r), hxne]
  rw [hvanish]
  simp [Nat.mod_eq_of_lt (Nat.lt_succ_self r)]

/-- Strict injectivity of the shell transform once one evaluates on the matching shell residue. -/
def conclusion_ramanujan_shell_transform_strict_injectivity_statement
    (a : ℕ → ℕ → ℤ) : Prop :=
  ∀ b : ℕ → ℕ → ℤ,
    (∀ ℓ r,
      conclusion_ramanujan_shell_transform_strict_injectivity_shell_transform a ℓ (r + 1) r =
        conclusion_ramanujan_shell_transform_strict_injectivity_shell_transform b ℓ (r + 1) r) →
      b = a

theorem paper_conclusion_ramanujan_shell_transform_strict_injectivity (a : ℕ → ℕ → ℤ) :
    conclusion_ramanujan_shell_transform_strict_injectivity_statement a := by
  intro b htransform
  funext ℓ r
  have hcoeff :
      conclusion_ramanujan_shell_transform_strict_injectivity_shell_transform a ℓ (r + 1) r =
        conclusion_ramanujan_shell_transform_strict_injectivity_shell_transform b ℓ (r + 1) r :=
    htransform ℓ r
  have hEq : a ℓ r = b ℓ r := by
    simpa [conclusion_ramanujan_shell_transform_strict_injectivity_shell_transform_recovers] using
      hcoeff
  simpa using hEq.symm

end Omega.Conclusion
