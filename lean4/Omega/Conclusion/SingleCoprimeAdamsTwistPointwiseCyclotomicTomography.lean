import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label:
`thm:conclusion-single-coprime-adams-twist-pointwise-cyclotomic-tomography`. -/
theorem paper_conclusion_single_coprime_adams_twist_pointwise_cyclotomic_tomography
    (M d : ℕ) (hM : 0 < M) (hd : Nat.Coprime d M) :
    Function.Bijective (fun z : ZMod M => (d : ZMod M) * z) := by
  haveI : NeZero M := ⟨Nat.pos_iff_ne_zero.mp hM⟩
  let u : (ZMod M)ˣ := ZMod.unitOfCoprime d hd
  simpa [u] using u.mulLeft_bijective

end Omega.Conclusion
