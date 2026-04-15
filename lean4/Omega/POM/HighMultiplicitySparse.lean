import Mathlib.Tactic
import Omega.Folding.FiberArithmetic

namespace Omega.POM

/-- High-multiplicity fibers are sparse: summing the lower bound
`α D_m ≤ d_m(x)` over the filtered set `S_α` and comparing with
`∑_x d_m(x) = 2^m` gives the counting bound.
    cor:pom-high-multiplicity-sparse -/
theorem paper_pom_high_multiplicity_sparse
    (m : ℕ) (α : ℚ) (hα0 : 0 < α) (_hα1 : α ≤ 1) :
    let Sα : Finset (Omega.X m) :=
      Finset.univ.filter (fun x =>
        α * (Omega.X.maxFiberMultiplicity m : ℚ) ≤
          (Omega.X.fiberMultiplicity x : ℚ));
    (Sα.card : ℚ) ≤
      (2 : ℚ) ^ m / (α * (Omega.X.maxFiberMultiplicity m : ℚ)) := by
  dsimp
  let Sα : Finset (Omega.X m) :=
    Finset.univ.filter (fun x =>
      α * (Omega.X.maxFiberMultiplicity m : ℚ) ≤
        (Omega.X.fiberMultiplicity x : ℚ))
  have hDpos : (0 : ℚ) < (Omega.X.maxFiberMultiplicity m : ℚ) := by
    exact_mod_cast Omega.X.maxFiberMultiplicity_pos m
  have hdenom : (0 : ℚ) < α * (Omega.X.maxFiberMultiplicity m : ℚ) :=
    mul_pos hα0 hDpos
  have hsum_lower :
      (Sα.card : ℚ) * (α * (Omega.X.maxFiberMultiplicity m : ℚ)) ≤
        Finset.sum Sα (fun x => (Omega.X.fiberMultiplicity x : ℚ)) := by
    calc
      (Sα.card : ℚ) * (α * (Omega.X.maxFiberMultiplicity m : ℚ))
          = Finset.sum Sα (fun _x => α * (Omega.X.maxFiberMultiplicity m : ℚ)) := by
              rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Finset.sum Sα (fun x => (Omega.X.fiberMultiplicity x : ℚ)) := by
            exact Finset.sum_le_sum fun x hx => (Finset.mem_filter.mp hx).2
  have hsum_upper :
      Finset.sum Sα (fun x => (Omega.X.fiberMultiplicity x : ℚ)) ≤
        Finset.univ.sum (fun x : Omega.X m => (Omega.X.fiberMultiplicity x : ℚ)) := by
    exact Finset.sum_le_univ_sum_of_nonneg fun _ => by positivity
  have hsum_total :
      Finset.univ.sum (fun x : Omega.X m => (Omega.X.fiberMultiplicity x : ℚ)) = (2 : ℚ) ^ m := by
    exact_mod_cast Omega.X.fiberMultiplicity_sum_eq_pow m
  have hmul :
      (Sα.card : ℚ) * (α * (Omega.X.maxFiberMultiplicity m : ℚ)) ≤ (2 : ℚ) ^ m := by
    calc
      (Sα.card : ℚ) * (α * (Omega.X.maxFiberMultiplicity m : ℚ))
          ≤ Finset.sum Sα (fun x => (Omega.X.fiberMultiplicity x : ℚ)) := hsum_lower
      _ ≤ Finset.univ.sum (fun x : Omega.X m => (Omega.X.fiberMultiplicity x : ℚ)) := hsum_upper
      _ = (2 : ℚ) ^ m := hsum_total
  exact (le_div_iff₀ hdenom).2 hmul

end Omega.POM
