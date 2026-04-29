import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic
import Omega.POM.FiberLeyangUnitcircleLiftCyclotomic
import Omega.POM.FiberPsiExponentMobiusReconstruct

namespace Omega.Conclusion

open Omega.UnitCirclePhaseArithmetic

/-- Paper label: `thm:conclusion-fiber-leyang-cyclotomic-fully-faithful-encoding`. The divisor
count vector `m_d` reconstructs the component-order histogram by the Möbius inversion theorem, and
for every recovered component order the path independent-set polynomial inherits the Lee--Yang
cyclotomic parametrization and the resulting unit-circle zeros. -/
theorem paper_conclusion_fiber_leyang_cyclotomic_fully_faithful_encoding
    (componentOrders : List ℕ) (m_d : ℕ → ℕ)
    (hOrders : ∀ n ∈ componentOrders, 3 ≤ n)
    (hm : ∀ d ≥ 3, m_d d = (componentOrders.filter fun n => d ∣ n).length) :
    (∃ c_n : ℕ → ℕ, ∀ n ≥ 3, c_n n = (componentOrders.filter fun m => m = n).length) ∧
      (∀ n ∈ componentOrders, Omega.pathIndSetPoly (n - 2) = Omega.fibPoly n) ∧
      (∀ n ∈ componentOrders, ∀ u : ℂ,
        u ≠ 1 → u ≠ -1 → u ^ n = 1 → ‖u‖ = 1 →
          (((Omega.pathIndSetPoly (n - 2)).map (Int.castRingHom ℂ)).eval (leyangJ u) = 0)) := by
  refine ⟨Omega.POM.paper_pom_fiber_psi_exponent_mobius_reconstruct componentOrders m_d hm, ?_, ?_⟩
  · intro n hn
    have hn2 : 2 ≤ n := by
      have hn3 : 3 ≤ n := hOrders n hn
      omega
    rcases Omega.paper_pom_path_indset_leyang_cyclotomic_param (n - 2) with ⟨hpoly, _⟩
    simpa [Nat.sub_add_cancel hn2] using hpoly
  · intro n hn u hu1 hum1 hu hu_unit
    have hn2 : 2 ≤ n := by
      have hn3 : 3 ≤ n := hOrders n hn
      omega
    let D : Omega.POM.pom_fiber_leyang_unitcircle_lift_cyclotomic_data :=
      { ell := n - 2
        u := u
        hu_ne_one := hu1
        hu_ne_neg_one := hum1
        hu_root := by simpa [Nat.sub_add_cancel hn2] using hu
        hu_unitcircle := hu_unit }
    exact (Omega.POM.paper_pom_fiber_leyang_unitcircle_lift_cyclotomic D).2.2.2.1

end Omega.Conclusion
