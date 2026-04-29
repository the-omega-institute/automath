import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:dephys-dirichlet-winding-minimal`. A constant visible readout on the
integer fiber forces any injective extended readout to be injective through its side information. -/
theorem paper_dephys_dirichlet_winding_minimal {S : Type*} (visible : Int -> Real × Real)
    (eta : Int -> S) (hvis : ∀ k, visible k = visible 0)
    (hinj : Function.Injective (fun k : Int => (visible k, eta k))) :
    ∃ iota : Int -> S, Function.Injective iota := by
  refine ⟨eta, ?_⟩
  intro a b hab
  apply hinj
  simp [hvis a, hvis b, hab]

end Omega.Zeta
