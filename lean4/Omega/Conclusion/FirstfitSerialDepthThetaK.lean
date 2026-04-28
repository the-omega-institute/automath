import Omega.POM.FractranFirstfitSerialDepth

namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-firstfit-serial-depth-theta-k`. -/
theorem paper_conclusion_firstfit_serial_depth_theta_k (k : Nat) (hk : 1 ≤ k) :
    ∃ c1 c2 : Nat,
      0 < c1 ∧ 0 < c2 ∧ c1 * k ≤ Omega.POM.fractranSerialDepth k ∧
        Omega.POM.fractranSerialDepth k ≤ c2 * k := by
  refine ⟨1, 1, by decide, by decide, ?_, ?_⟩
  · simpa only [one_mul] using (Omega.POM.paper_pom_fractran_firstfit_serial_depth k hk).2
  · have hdepth : Omega.POM.fractranSerialDepth k = k := by
      unfold Omega.POM.fractranSerialDepth
      exact Finset.card_range k
    rw [hdepth, one_mul]

end Omega.Conclusion
