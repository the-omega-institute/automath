import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

/-- Paper label: `thm:pom-occupancy-functional-collision-expansion`. -/
theorem paper_pom_occupancy_functional_collision_expansion {α : Type*} [Fintype α]
    [DecidableEq α] (w : α → ℂ) (coeff : ℕ → ℂ) (n Q : ℕ) :
    Finset.univ.sum
        (fun x =>
          w x *
            Finset.sum (Finset.range (Q + 1))
              (fun q => coeff q * (n : ℂ) ^ q * (w x) ^ q)) =
      Finset.sum (Finset.range (Q + 1))
        (fun q => coeff q * (n : ℂ) ^ q * Finset.univ.sum (fun x => (w x) ^ (q + 1))) := by
  calc
    Finset.univ.sum
        (fun x =>
          w x *
            Finset.sum (Finset.range (Q + 1))
              (fun q => coeff q * (n : ℂ) ^ q * (w x) ^ q))
        = Finset.univ.sum
            (fun x =>
              Finset.sum (Finset.range (Q + 1))
                (fun q => w x * (coeff q * (n : ℂ) ^ q * (w x) ^ q))) := by
          simp [Finset.mul_sum]
    _ = Finset.sum (Finset.range (Q + 1))
          (fun q =>
            Finset.univ.sum
              (fun x => w x * (coeff q * (n : ℂ) ^ q * (w x) ^ q))) := by
          rw [Finset.sum_comm]
    _ = Finset.sum (Finset.range (Q + 1))
          (fun q => coeff q * (n : ℂ) ^ q * Finset.univ.sum (fun x => (w x) ^ (q + 1))) := by
          refine Finset.sum_congr rfl ?_
          intro q _
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro x _
          rw [pow_succ]
          ring

end Omega.POM
