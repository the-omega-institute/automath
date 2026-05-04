import Omega.Conclusion.GodelTateBadicPrefixTree

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-godel-dyadic-tate-filament`. -/
theorem paper_conclusion_godel_dyadic_tate_filament (M L k : Nat) (hB : M < 2 ^ L) :
    ∀ a b : Fin k → Fin (M + 1),
      (∑ t : Fin k, (a t : Nat) * (2 ^ L) ^ (t : Nat)) =
        (∑ t : Fin k, (b t : Nat) * (2 ^ L) ^ (t : Nat)) →
      a = b := by
  exact (paper_conclusion_godel_tate_badic_prefix_tree M (2 ^ L) k 0 hB (Nat.zero_le k)).1

end Omega.Conclusion
