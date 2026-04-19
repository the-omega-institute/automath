import Mathlib.Tactic
import Omega.Folding.Fiber
import Omega.Folding.HammingDist

/-!
# Majority seed for the fiber triple median

This file registers the paper-facing seed/package wrapper for
`thm:pom-fiber-triple-median-majority`.
-/

namespace Omega.POM.FiberTripleMedianMajority

/-- Boolean majority on three inputs. -/
def majority3 (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

/-- The Boolean majority minimizes the three-point Hamming cost. -/
theorem majority3_minimizes_hamming (a b c t : Bool) :
    (if majority3 a b c ≠ a then 1 else 0) +
      (if majority3 a b c ≠ b then 1 else 0) +
      (if majority3 a b c ≠ c then 1 else 0) ≤
    (if t ≠ a then 1 else 0) +
      (if t ≠ b then 1 else 0) +
      (if t ≠ c then 1 else 0) := by
  cases a <;> cases b <;> cases c <;> cases t <;> decide

/-- Paper seed for the triple-median majority formula.
    thm:pom-fiber-triple-median-majority -/
theorem paper_pom_fiber_triple_median_majority_seeds (a b c t : Bool) :
    (if majority3 a b c ≠ a then 1 else 0) +
      (if majority3 a b c ≠ b then 1 else 0) +
      (if majority3 a b c ≠ c then 1 else 0) ≤
    (if t ≠ a then 1 else 0) +
      (if t ≠ b then 1 else 0) +
      (if t ≠ c then 1 else 0) :=
  majority3_minimizes_hamming a b c t

/-- Packaged form of the triple-median majority formula.
    thm:pom-fiber-triple-median-majority -/
theorem paper_pom_fiber_triple_median_majority_package (a b c t : Bool) :
    (if majority3 a b c ≠ a then 1 else 0) +
      (if majority3 a b c ≠ b then 1 else 0) +
      (if majority3 a b c ≠ c then 1 else 0) ≤
    (if t ≠ a then 1 else 0) +
      (if t ≠ b then 1 else 0) +
      (if t ≠ c then 1 else 0) :=
  paper_pom_fiber_triple_median_majority_seeds a b c t

end Omega.POM.FiberTripleMedianMajority

namespace Omega.POM

/-- A fiberwise Hamming median exists for every triple of points in the same folding fiber.
    thm:pom-fiber-triple-median-majority -/
theorem paper_pom_fiber_triple_median_majority {m : Nat} (x : Omega.X m)
    (a b c : Omega.X.FiberElem x) :
    ∃ med : Omega.X.FiberElem x, ∀ t : Omega.X.FiberElem x,
      Omega.hammingDist a.1 med.1 + Omega.hammingDist b.1 med.1 +
          Omega.hammingDist c.1 med.1 ≤
        Omega.hammingDist a.1 t.1 + Omega.hammingDist b.1 t.1 + Omega.hammingDist c.1 t.1 := by
  classical
  let cost : Omega.X.FiberElem x → Nat := fun w =>
    Omega.hammingDist a.1 w.1 + Omega.hammingDist b.1 w.1 + Omega.hammingDist c.1 w.1
  let witness : Omega.X.FiberElem x :=
    ⟨Omega.X.choosePreimage x, Omega.X.choosePreimage_mem_fiber x⟩
  let costs : Finset Nat := Finset.univ.image cost
  have hcosts_nonempty : costs.Nonempty := by
    refine ⟨cost witness, ?_⟩
    simp [costs, witness]
  let minCost := costs.min' hcosts_nonempty
  have hmin_mem : minCost ∈ costs := Finset.min'_mem costs hcosts_nonempty
  have hmin_mem' : minCost ∈ Finset.univ.image cost := by
    simpa [costs] using hmin_mem
  rcases Finset.mem_image.mp hmin_mem' with ⟨med, -, hmed⟩
  refine ⟨med, ?_⟩
  intro t
  have ht : cost t ∈ costs := by
    simp [costs]
  have hmin_le : minCost ≤ cost t := Finset.min'_le costs _ ht
  have hmed_le_t : cost med ≤ cost t := by
    rw [hmed]
    exact hmin_le
  simpa [cost] using hmed_le_t

end Omega.POM
