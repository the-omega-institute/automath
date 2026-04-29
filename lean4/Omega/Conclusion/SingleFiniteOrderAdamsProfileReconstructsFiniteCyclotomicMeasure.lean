import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label:
`cor:conclusion-single-finite-order-adams-profile-reconstructs-finite-cyclotomic-measure`. -/
theorem paper_conclusion_single_finite_order_adams_profile_reconstructs_finite_cyclotomic_measure
    (M d N : ℕ) (hM : 0 < M) (hd : Nat.Coprime d M) (hN : M - 1 ≤ N) :
    Function.Surjective
      (fun m : {m : ℤ // -(N : ℤ) ≤ m ∧ m ≤ (N : ℤ)} =>
        (-(d : ZMod M)) * (m.1 : ZMod M)) := by
  haveI : NeZero M := ⟨Nat.pos_iff_ne_zero.mp hM⟩
  intro y
  let u : (ZMod M)ˣ := -ZMod.unitOfCoprime d hd
  let z : ZMod M := (u⁻¹ : (ZMod M)ˣ) * y
  refine ⟨⟨(z.val : ℤ), ?_⟩, ?_⟩
  · constructor
    · omega
    · have hlt : z.val < M := ZMod.val_lt z
      have hle : z.val ≤ N := by omega
      exact_mod_cast hle
  · calc
      (-(d : ZMod M)) * ((z.val : ℤ) : ZMod M) = (u : ZMod M) * z := by
        simp [u]
      _ = y := by
        simp [z]

end Omega.Conclusion
