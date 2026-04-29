import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-window6-raw-affine-conductor-shift`. -/
theorem paper_conclusion_window6_raw_affine_conductor_shift :
    (let c3 : Fin 21 → ℤ := fun r => if 3 ∣ r.val then 2 else -1;
      let c7 : Fin 21 → ℤ := fun r => if 7 ∣ r.val then 6 else -1;
      let c21 : Fin 21 → ℤ := fun r => c3 r * c7 r;
      let d : Fin 21 → ℤ := fun r => if r.val ≤ 8 then 4 else if r.val ≤ 12 then 3 else 2;
      let deltaAff : Fin 21 → ℤ := fun r =>
        (if r.val ∈ ({1, 2, 3, 5, 6, 7} : Finset Nat) then 4 else 0) +
          (if r.val ∈ ({9, 10, 11, 12} : Finset Nat) then 1 else 0);
      let a : Fin 21 → ℤ := fun r => d r + deltaAff r;
      Finset.univ.sum (fun r => d r * c3 r) = 2 ∧
        Finset.univ.sum (fun r => d r * c7 r) = 6 ∧
        Finset.univ.sum (fun r => d r * c21 r) = 12 ∧
        Finset.univ.sum (fun r => a r * c3 r) = 4 ∧
        Finset.univ.sum (fun r => a r * c7 r) = 6 ∧
        Finset.univ.sum (fun r => a r * c21 r) = -18) := by
  native_decide

end Omega.Conclusion
