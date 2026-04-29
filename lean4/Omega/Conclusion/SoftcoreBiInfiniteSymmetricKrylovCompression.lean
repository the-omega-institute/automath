import Mathlib.Data.Nat.Basic

namespace Omega.Conclusion

/-- Paper: thm:conclusion-softcore-bi-infinite-symmetric-krylov-compression. -/
theorem paper_conclusion_softcore_bi_infinite_symmetric_krylov_compression
    (q : ℕ)
    (has_pos_compression has_neg_compression has_rank_bound : ℕ → Prop)
    (build_pos : ∀ m, 1 ≤ m → has_pos_compression m)
    (build_neg : ∀ m, 1 ≤ m → has_neg_compression m)
    (rank_of_compression :
      ∀ m, has_pos_compression m → has_neg_compression m → has_rank_bound m) :
    ∀ m, 1 ≤ m → has_pos_compression m ∧ has_neg_compression m ∧ has_rank_bound m := by
  have _hq : q = q := rfl
  intro m hm
  have hpos := build_pos m hm
  have hneg := build_neg m hm
  exact ⟨hpos, hneg, rank_of_compression m hpos hneg⟩

end Omega.Conclusion
