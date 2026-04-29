import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete finite-certificate data for self-reciprocal leakage-pair detection.  The fields record
the finite CMV certificate, a leakage-pair predicate along the stages, and the minimal certificate
depth.  The escape hypothesis is the bounded-depth contradiction produced by finite-certificate
freezing and finite-defect detectability. -/
structure conclusion_selfreciprocal_leakage_pairs_expelled_to_infinite_depth_data where
  conclusion_selfreciprocal_leakage_pairs_expelled_to_infinite_depth_certificate :
    ℕ → ℕ → Bool
  conclusion_selfreciprocal_leakage_pairs_expelled_to_infinite_depth_leakagePair :
    ℕ → Bool
  conclusion_selfreciprocal_leakage_pairs_expelled_to_infinite_depth_minDepth :
    ℕ → ℕ
  conclusion_selfreciprocal_leakage_pairs_expelled_to_infinite_depth_detects :
    ∀ L : ℕ,
      conclusion_selfreciprocal_leakage_pairs_expelled_to_infinite_depth_leakagePair L = true →
        conclusion_selfreciprocal_leakage_pairs_expelled_to_infinite_depth_certificate
            (conclusion_selfreciprocal_leakage_pairs_expelled_to_infinite_depth_minDepth L) L =
          true
  conclusion_selfreciprocal_leakage_pairs_expelled_to_infinite_depth_minDepth_escape :
    ∀ B : ℕ, ∃ L0 : ℕ, ∀ L : ℕ, L0 ≤ L →
      B <
        conclusion_selfreciprocal_leakage_pairs_expelled_to_infinite_depth_minDepth L

namespace conclusion_selfreciprocal_leakage_pairs_expelled_to_infinite_depth_data

/-- The least finite certificate depth escapes every fixed bound. -/
def conclusion_selfreciprocal_leakage_pairs_expelled_to_infinite_depth_min_depth_tends_to_infinity
    (D : conclusion_selfreciprocal_leakage_pairs_expelled_to_infinite_depth_data) : Prop :=
  ∀ B : ℕ, ∃ L0 : ℕ, ∀ L : ℕ, L0 ≤ L →
    B < D.conclusion_selfreciprocal_leakage_pairs_expelled_to_infinite_depth_minDepth L

/-- A uniformly bounded long-term leakage detector would bound the least detecting depth on a
tail of stages. -/
def
    conclusion_selfreciprocal_leakage_pairs_expelled_to_infinite_depth_uniform_bounded_long_term_leakage
    (D : conclusion_selfreciprocal_leakage_pairs_expelled_to_infinite_depth_data) : Prop :=
  ∃ B L0 : ℕ, ∀ L : ℕ, L0 ≤ L →
    D.conclusion_selfreciprocal_leakage_pairs_expelled_to_infinite_depth_minDepth L ≤ B

end conclusion_selfreciprocal_leakage_pairs_expelled_to_infinite_depth_data

/-- Paper label: `thm:conclusion-selfreciprocal-leakage-pairs-expelled-to-infinite-depth`. -/
theorem paper_conclusion_selfreciprocal_leakage_pairs_expelled_to_infinite_depth
    (D : conclusion_selfreciprocal_leakage_pairs_expelled_to_infinite_depth_data) :
    D.conclusion_selfreciprocal_leakage_pairs_expelled_to_infinite_depth_min_depth_tends_to_infinity ∧
      ¬
        D.conclusion_selfreciprocal_leakage_pairs_expelled_to_infinite_depth_uniform_bounded_long_term_leakage := by
  refine
    ⟨D.conclusion_selfreciprocal_leakage_pairs_expelled_to_infinite_depth_minDepth_escape, ?_⟩
  intro hbounded
  rcases hbounded with ⟨B, L0, hB⟩
  rcases D.conclusion_selfreciprocal_leakage_pairs_expelled_to_infinite_depth_minDepth_escape B with
    ⟨L1, hescape⟩
  let L := max L0 L1
  have hle :
      D.conclusion_selfreciprocal_leakage_pairs_expelled_to_infinite_depth_minDepth L ≤ B :=
    hB L (Nat.le_max_left L0 L1)
  have hlt :
      B < D.conclusion_selfreciprocal_leakage_pairs_expelled_to_infinite_depth_minDepth L :=
    hescape L (Nat.le_max_right L0 L1)
  exact (not_lt_of_ge hle) hlt

end Omega.Conclusion
