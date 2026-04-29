import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic
import Omega.POM.LeyangLiftMobiusInvolutionFunctorial
import Omega.POM.PathIndsetLeyangCyclotomicParam

namespace Omega.POM

open Omega.UnitCirclePhaseArithmetic

/-- Concrete data for the lifted Lee--Yang fiber packet on the unit circle. The nontrivial root of
unity `u` is recorded together with its unit-circle modulus. -/
structure pom_fiber_leyang_unitcircle_lift_cyclotomic_data where
  ell : ℕ
  u : ℂ
  hu_ne_one : u ≠ 1
  hu_ne_neg_one : u ≠ -1
  hu_root : u ^ (ell + 2) = 1
  hu_unitcircle : ‖u‖ = 1

/-- The path independent-set polynomial is the shifted Fibonacci polynomial, the Lee--Yang lift and
the Möbius involution commute on that polynomial, and every recorded nontrivial cyclotomic point
on the unit circle is a zero of the Lee--Yang fiber evaluation. -/
def pom_fiber_leyang_unitcircle_lift_cyclotomic_statement
    (h : pom_fiber_leyang_unitcircle_lift_cyclotomic_data) : Prop :=
  Omega.pathIndSetPoly h.ell = Omega.fibPoly (h.ell + 2) ∧
    Omega.POM.leyangLift (Omega.POM.mobiusInvolution (Omega.pathIndSetPoly h.ell)) =
      Omega.POM.mobiusInvolution (Omega.POM.leyangLift (Omega.pathIndSetPoly h.ell)) ∧
    Omega.PathIndSetLeyangCyclotomicRoots h.ell ∧
    (((Omega.pathIndSetPoly h.ell).map (Int.castRingHom ℂ)).eval (leyangJ h.u) = 0) ∧
    ‖h.u‖ = 1

/-- Paper label: `prop:pom-fiber-leyang-unitcircle-lift-cyclotomic`. -/
theorem paper_pom_fiber_leyang_unitcircle_lift_cyclotomic
    (h : pom_fiber_leyang_unitcircle_lift_cyclotomic_data) :
    pom_fiber_leyang_unitcircle_lift_cyclotomic_statement h := by
  rcases Omega.paper_pom_path_indset_leyang_cyclotomic_param h.ell with ⟨hfib, hroots⟩
  refine ⟨hfib, ?_, hroots, ?_, h.hu_unitcircle⟩
  · simpa using Omega.POM.leyangLift_mobius_exchange (Omega.pathIndSetPoly h.ell)
  · exact hroots h.u h.hu_ne_one h.hu_ne_neg_one h.hu_root

end Omega.POM
