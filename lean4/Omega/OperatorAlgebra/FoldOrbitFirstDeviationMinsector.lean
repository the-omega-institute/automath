import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic
import Omega.OperatorAlgebra.FoldOrbitTouchardLoworder

namespace Omega.OperatorAlgebra

open scoped BigOperators

/-- The first degree at which the truncated orbit count can differ from the unrestricted Touchard
count. -/
def foldOrbitFirstDeviationOrder (dmin : ℕ) : ℕ :=
  dmin + 1

/-- The number of sectors whose degeneracy attains the minimum value `dmin`. -/
def foldOrbitMinsectorCount {m : ℕ} (N : Fin m → ℕ) (dmin : ℕ) : ℕ :=
  (Finset.univ.filter fun d : Fin m => N d = dmin).card

/-- At the first deviation order, each minimal sector contributes exactly one missing partition. -/
def foldOrbitFirstDeviationCorrection {m : ℕ} (N : Fin m → ℕ) (dmin : ℕ) : ℕ :=
  Finset.sum Finset.univ (fun d : Fin m => if N d = dmin then 1 else 0)

/-- Model orbit count at the first degree where the truncation becomes visible. -/
def foldOrbitFirstDeviationOrbitCount {m : ℕ} (N : Fin m → ℕ) (dmin : ℕ) : ℕ :=
  touchardPolynomial (foldOrbitFirstDeviationOrder dmin) m -
    foldOrbitFirstDeviationCorrection N dmin

/-- At `q₀ = d_min + 1`, exactly the minimal-degeneracy sectors lose one Bell partition, so the
first Burnside orbit count differs from the Touchard value by the size of the minimal sector.
    prop:op-algebra-fold-orbit-first-deviation-minsector -/
theorem paper_op_algebra_fold_orbit_first_deviation_minsector {m : ℕ}
    (N : Fin m → ℕ) (dmin : ℕ) :
    foldOrbitFirstDeviationOrbitCount N dmin =
      touchardPolynomial (foldOrbitFirstDeviationOrder dmin) m - foldOrbitMinsectorCount N dmin :=
by
  have hcorr : foldOrbitFirstDeviationCorrection N dmin = foldOrbitMinsectorCount N dmin := by
    unfold foldOrbitFirstDeviationCorrection foldOrbitMinsectorCount
    calc
      Finset.sum Finset.univ (fun d : Fin m => if N d = dmin then 1 else 0)
          = Finset.sum (Finset.univ.filter (fun d : Fin m => N d = dmin)) (fun _ => (1 : ℕ)) := by
              symm
              simpa using
                (Finset.sum_filter (s := Finset.univ) (p := fun d : Fin m => N d = dmin)
                  (f := fun _ => (1 : ℕ)))
      _ = (Finset.univ.filter fun d : Fin m => N d = dmin).card := by simp
  rw [foldOrbitFirstDeviationOrbitCount, hcorr]

end Omega.OperatorAlgebra
