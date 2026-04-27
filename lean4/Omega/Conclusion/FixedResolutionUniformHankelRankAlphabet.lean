import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-fixedresolution-uniform-hankel-rank-alphabet`. -/
theorem paper_conclusion_fixedresolution_uniform_hankel_rank_alphabet
    (D : ℕ) (_hD : 1 ≤ D) (M : Set ℕ) (s recurrenceOrder : ℕ → ℕ)
    (hankelRank : ℕ → ℕ → ℕ) (detVanishes : ℕ → Prop)
    (hRank : ∀ m ∈ M, ∀ r : ℕ, hankelRank m r = min (r + 1) (s m))
    (hDet : ∀ m ∈ M, detVanishes m ↔ hankelRank m D ≤ D)
    (hRec : ∀ m ∈ M, recurrenceOrder m = s m) :
    ((∀ m ∈ M, s m ≤ D) ↔
      (∀ m ∈ M, ∀ r : ℕ, hankelRank m r ≤ D) ∧
        (∀ m ∈ M, detVanishes m) ∧
          (∀ m ∈ M, recurrenceOrder m ≤ D)) := by
  constructor
  · intro hs
    refine ⟨?_, ?_, ?_⟩
    · intro m hm r
      have hmin : min (r + 1) (s m) ≤ D :=
        le_trans (Nat.min_le_right (r + 1) (s m)) (hs m hm)
      simpa [hRank m hm r] using hmin
    · intro m hm
      exact (hDet m hm).mpr (by simpa using
        (show hankelRank m D ≤ D from
          by
            have hmin : min (D + 1) (s m) ≤ D :=
              le_trans (Nat.min_le_right (D + 1) (s m)) (hs m hm)
            simpa [hRank m hm D] using hmin))
    · intro m hm
      simpa [hRec m hm] using hs m hm
  · intro hpack m hm
    exact (by simpa [hRec m hm] using hpack.2.2 m hm)

end Omega.Conclusion
