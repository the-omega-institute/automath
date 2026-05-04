import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-affine-defect-ramanujan-moments`. -/
theorem paper_conclusion_window6_affine_defect_ramanujan_moments :
    (let c3 : Fin 21 → ℤ := fun r => if 3 ∣ r.val then 2 else -1
     let c7 : Fin 21 → ℤ := fun r => if 7 ∣ r.val then 6 else -1
     let c21 : Fin 21 → ℤ := fun r => c3 r * c7 r
     let deltaAff : Fin 21 → ℤ := fun r =>
       (if r.val ∈ ({1, 2, 3, 5, 6, 7} : Finset Nat) then 4 else 0) +
         (if r.val ∈ ({9, 10, 11, 12} : Finset Nat) then 1 else 0)
     Finset.univ.sum (fun r => deltaAff r * c3 r) = 2 ∧
       Finset.univ.sum (fun r => deltaAff r * c7 r) = 0 ∧
       Finset.univ.sum (fun r => deltaAff r * c21 r) = -30) := by
  native_decide

end Omega.Conclusion
