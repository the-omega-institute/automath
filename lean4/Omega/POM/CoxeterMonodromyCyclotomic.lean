import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic

namespace Omega.POM

open Polynomial

/-- The characteristic polynomial contributed by a single `d`-cycle block. -/
noncomputable def pom_coxeter_monodromy_cyclotomic_cycle_charpoly (d : ℕ) : Polynomial ℤ :=
  X ^ d - 1

/-- The determinant/sign contributed by a single `d`-cycle block. -/
def pom_coxeter_monodromy_cyclotomic_cycle_det (d : ℕ) : ℤ :=
  (-1 : ℤ) ^ (d - 1)

/-- The trace contributed by a single `d`-cycle block: only fixed points contribute. -/
def pom_coxeter_monodromy_cyclotomic_cycle_trace (d : ℕ) : ℕ :=
  if d = 1 then 1 else 0

/-- The block-diagonal characteristic polynomial is the product of the cycle-block factors. -/
noncomputable def pom_coxeter_monodromy_cyclotomic_fiber_charpoly
    (cycleLengths : List ℕ) : Polynomial ℤ :=
  (cycleLengths.map pom_coxeter_monodromy_cyclotomic_cycle_charpoly).prod

/-- The block-diagonal determinant is the product of the cycle-block signs. -/
def pom_coxeter_monodromy_cyclotomic_fiber_det (cycleLengths : List ℕ) : ℤ :=
  (cycleLengths.map pom_coxeter_monodromy_cyclotomic_cycle_det).prod

/-- The block-diagonal trace is the sum of the cycle-block traces. -/
def pom_coxeter_monodromy_cyclotomic_fiber_trace (cycleLengths : List ℕ) : ℕ :=
  (cycleLengths.map pom_coxeter_monodromy_cyclotomic_cycle_trace).sum

/-- The number of fixed points is the number of `1`-cycles. -/
def pom_coxeter_monodromy_cyclotomic_fiber_fixed_points (cycleLengths : List ℕ) : ℕ :=
  cycleLengths.count 1

private lemma pom_coxeter_monodromy_cyclotomic_fiber_trace_eq_fixed_points
    (cycleLengths : List ℕ) :
    pom_coxeter_monodromy_cyclotomic_fiber_trace cycleLengths =
      pom_coxeter_monodromy_cyclotomic_fiber_fixed_points cycleLengths := by
  induction cycleLengths with
  | nil =>
      simp [pom_coxeter_monodromy_cyclotomic_fiber_trace,
        pom_coxeter_monodromy_cyclotomic_fiber_fixed_points]
  | cons d ds ih =>
      by_cases hd : d = 1
      · subst hd
        simpa [pom_coxeter_monodromy_cyclotomic_fiber_trace,
          pom_coxeter_monodromy_cyclotomic_fiber_fixed_points,
          pom_coxeter_monodromy_cyclotomic_cycle_trace, Nat.add_comm] using congrArg Nat.succ ih
      · simpa [pom_coxeter_monodromy_cyclotomic_fiber_trace,
          pom_coxeter_monodromy_cyclotomic_fiber_fixed_points,
          pom_coxeter_monodromy_cyclotomic_cycle_trace, hd] using ih

/-- Paper label: `thm:pom-coxeter-monodromy-cyclotomic`. The scan monodromy is modeled as a
permutation decomposed into cycle blocks; each `d`-cycle contributes the cyclotomic factor
`X^d - 1`, determinant/sign `(-1)^(d-1)`, and trace equal to its fixed-point count, and the
general fiber package is obtained by multiplying/summing the block contributions. -/
theorem paper_pom_coxeter_monodromy_cyclotomic (cycleLengths : List ℕ) :
    (∀ d ∈ cycleLengths,
      pom_coxeter_monodromy_cyclotomic_cycle_charpoly d = X ^ d - 1 ∧
        pom_coxeter_monodromy_cyclotomic_cycle_det d = (-1 : ℤ) ^ (d - 1) ∧
        pom_coxeter_monodromy_cyclotomic_cycle_trace d = if d = 1 then 1 else 0) ∧
      pom_coxeter_monodromy_cyclotomic_fiber_charpoly cycleLengths =
        (cycleLengths.map pom_coxeter_monodromy_cyclotomic_cycle_charpoly).prod ∧
      pom_coxeter_monodromy_cyclotomic_fiber_det cycleLengths =
        (cycleLengths.map pom_coxeter_monodromy_cyclotomic_cycle_det).prod ∧
      pom_coxeter_monodromy_cyclotomic_fiber_trace cycleLengths =
        (cycleLengths.map pom_coxeter_monodromy_cyclotomic_cycle_trace).sum ∧
      pom_coxeter_monodromy_cyclotomic_fiber_trace cycleLengths =
        pom_coxeter_monodromy_cyclotomic_fiber_fixed_points cycleLengths := by
  refine ⟨?_, rfl, rfl, rfl, pom_coxeter_monodromy_cyclotomic_fiber_trace_eq_fixed_points cycleLengths⟩
  intro d hd
  simp [pom_coxeter_monodromy_cyclotomic_cycle_charpoly,
    pom_coxeter_monodromy_cyclotomic_cycle_det, pom_coxeter_monodromy_cyclotomic_cycle_trace]

end Omega.POM
