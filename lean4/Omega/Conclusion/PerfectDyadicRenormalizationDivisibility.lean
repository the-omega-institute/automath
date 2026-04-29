import Mathlib.Tactic

namespace Omega.Conclusion

universe u

/-- Paper label: `cor:conclusion-perfect-dyadic-renormalization-divisibility`. -/
theorem paper_conclusion_perfect_dyadic_renormalization_divisibility {ι : Type u}
    [Fintype ι] (d : ι → Nat) (B : Nat) :
    (let M := 2 ^ B
     let defect : Nat := Finset.univ.sum (fun x => (d x % M) * (M - d x % M))
     defect = 0 ↔ ∀ x, M ∣ d x) := by
  dsimp
  constructor
  · intro hdefect x
    have hterm :
        (d x % 2 ^ B) * (2 ^ B - d x % 2 ^ B) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
        (fun y _hy => Nat.zero_le ((d y % 2 ^ B) * (2 ^ B - d y % 2 ^ B)))).mp
        hdefect x (Finset.mem_univ x)
    have hpos : 0 < 2 ^ B := pow_pos (by norm_num) B
    have hlt : d x % 2 ^ B < 2 ^ B := Nat.mod_lt (d x) hpos
    have hmod : d x % 2 ^ B = 0 := by
      rcases Nat.mul_eq_zero.mp hterm with hzero | hsub
      · exact hzero
      · have hle : 2 ^ B ≤ d x % 2 ^ B := Nat.le_of_sub_eq_zero hsub
        omega
    exact Nat.dvd_iff_mod_eq_zero.mpr hmod
  · intro hdvd
    refine Finset.sum_eq_zero ?_
    intro x _hx
    have hmod : d x % 2 ^ B = 0 := Nat.mod_eq_zero_of_dvd (hdvd x)
    simp [hmod]

end Omega.Conclusion
