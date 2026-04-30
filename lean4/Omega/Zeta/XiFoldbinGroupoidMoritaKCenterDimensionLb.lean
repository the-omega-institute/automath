import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-foldbin-groupoid-morita-k-center-dimension-lb`. -/
theorem paper_xi_foldbin_groupoid_morita_k_center_dimension_lb (fiberSizes : List Nat)
    (total : Nat) (moritaKCenterPackage : Prop) (hMoritaKCenter : moritaKCenterPackage)
    (hTotal : fiberSizes.sum = total) :
    moritaKCenterPackage ∧
      total ^ 2 ≤ fiberSizes.length * (fiberSizes.map (fun d => d ^ 2)).sum := by
  constructor
  · exact hMoritaKCenter
  · subst total
    have hcs :
        (∑ i : Fin fiberSizes.length, fiberSizes.get i) ^ 2 ≤
          Fintype.card (Fin fiberSizes.length) *
            ∑ i : Fin fiberSizes.length, (fiberSizes.get i) ^ 2 := by
      simpa using
        (sq_sum_le_card_mul_sum_sq
          (s := (Finset.univ : Finset (Fin fiberSizes.length)))
          (f := fun i : Fin fiberSizes.length => fiberSizes.get i))
    have hsquares :
        (∑ i : Fin fiberSizes.length, (fiberSizes.get i) ^ 2) =
          (fiberSizes.map (fun d => d ^ 2)).sum := by
      rw [← Fin.sum_ofFn]
      have hofn :
          List.ofFn (fun i : Fin fiberSizes.length => (fiberSizes.get i) ^ 2) =
            fiberSizes.map (fun d => d ^ 2) := by
        simpa [Function.comp_def] using
          (List.ofFn_comp' (f := fiberSizes.get) (g := fun d : Nat => d ^ 2))
      exact congrArg List.sum hofn
    calc
      fiberSizes.sum ^ 2 ≤ fiberSizes.length *
          ∑ i : Fin fiberSizes.length, (fiberSizes.get i) ^ 2 := by
        simpa [Fin.sum_ofFn, List.ofFn_get] using hcs
      _ = fiberSizes.length * (fiberSizes.map (fun d => d ^ 2)).sum := by
        rw [hsquares]

end Omega.Zeta
