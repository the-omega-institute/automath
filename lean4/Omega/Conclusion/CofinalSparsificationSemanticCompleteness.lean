import Mathlib.Tactic

namespace Omega.Conclusion

/-- Chapter-local concrete package for the conclusion-level cofinal sparsification theorem. The
semantics live on a fixed carrier, are rigid under refinement, and the minimal realization
dimension is uniformly bounded. -/
structure ConclusionCofinalSparsificationSemanticCompletenessData where
  Carrier : Type
  semantics : ℕ → Carrier → Prop
  subseq : ℕ → ℕ
  subseqStrictMono : StrictMono subseq
  semanticsRigid : ∀ {m n : ℕ}, m ≤ n → ∀ x : Carrier, semantics m x ↔ semantics n x
  minimalDimension : ℕ → ℕ
  dimensionBound : ℕ
  boundedDimension : ∀ b, minimalDimension b ≤ dimensionBound

/-- Semantic completeness along the chosen cofinal subsequence. -/
def ConclusionCofinalSparsificationSemanticCompletenessData.cofinalReconstruction
    (D : ConclusionCofinalSparsificationSemanticCompletenessData) : Prop :=
  ∀ b x, D.semantics b x ↔ D.semantics (D.subseq b) x

/-- Uniform bounded dimension collapses the semantics to a single finite level. -/
def ConclusionCofinalSparsificationSemanticCompletenessData.finiteLevelDetermination
    (D : ConclusionCofinalSparsificationSemanticCompletenessData) : Prop :=
  ∃ bStar ≤ D.dimensionBound, ∀ b x, D.semantics b x ↔ D.semantics bStar x

private theorem strictMono_ge_self (f : ℕ → ℕ) (hf : StrictMono f) :
    ∀ n, n ≤ f n := by
  intro n
  induction' n with n ih
  · exact Nat.zero_le _
  · have hstep : f n < f (n + 1) := hf (Nat.lt_succ_self n)
    omega

/-- Deterministic semantics are unchanged on any cofinal subsequence, and a uniform bound on the
minimal realization dimension collapses the whole tower to one finite level.
    thm:conclusion-cofinal-sparsification-semantic-completeness -/
theorem paper_conclusion_cofinal_sparsification_semantic_completeness
    (D : ConclusionCofinalSparsificationSemanticCompletenessData) :
    D.cofinalReconstruction ∧ D.finiteLevelDetermination := by
  refine ⟨?_, ?_⟩
  · intro b x
    exact D.semanticsRigid (strictMono_ge_self D.subseq D.subseqStrictMono b) x
  · refine ⟨D.dimensionBound, le_rfl, ?_⟩
    intro b x
    by_cases h : b ≤ D.dimensionBound
    · exact D.semanticsRigid h x
    · exact (D.semanticsRigid (le_of_not_ge h) x).symm

end Omega.Conclusion
