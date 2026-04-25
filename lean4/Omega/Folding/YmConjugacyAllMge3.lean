import Omega.Folding.PhiConjugacyThreshold
import Mathlib.Tactic

namespace Omega.Folding

set_option maxHeartbeats 400000 in
/-- Above the `m = 3` threshold, the paper's cross-chapter conjugacy map
`h_{m → n} := Φ_n ∘ Ψ_m` is just the identity code, so it is bijective and
commutes with the shift.
    cor:Ym-conjugacy-all-mge3 -/
theorem paper_Ym_conjugacy_all_mge3 :
    ∀ m n : ℕ, 3 ≤ m → 3 ≤ n →
      Function.Bijective
          (fun y : ℤ → Bool => PhiConjugacySeed n (PsiConjugacySeed m y)) ∧
        (∀ y : ℤ → Bool,
          PhiConjugacySeed n (PsiConjugacySeed m (shiftSeq y)) =
            shiftSeq (PhiConjugacySeed n (PsiConjugacySeed m y))) := by
  intro m n hm hn
  constructor
  · constructor
    · intro y₁ y₂ h
      simpa [PsiConjugacySeed, PhiConjugacySeed_eq_id hn] using h
    · intro y
      refine ⟨y, ?_⟩
      simp [PsiConjugacySeed, PhiConjugacySeed_eq_id hn]
  · intro y
    simp [PsiConjugacySeed, PhiConjugacySeed_eq_id hn]

/-- Lowercase paper-facing alias for the stabilized conjugacy collapse.
    cor:Ym-conjugacy-all-mge3 -/
theorem paper_ym_conjugacy_all_mge3 :
    ∀ m n : ℕ, 3 ≤ m → 3 ≤ n →
      Function.Bijective
          (fun y : ℤ → Bool => PhiConjugacySeed n (PsiConjugacySeed m y)) ∧
        (∀ y : ℤ → Bool,
          PhiConjugacySeed n (PsiConjugacySeed m (shiftSeq y)) =
            shiftSeq (PhiConjugacySeed n (PsiConjugacySeed m y))) := by
  simpa using paper_Ym_conjugacy_all_mge3

end Omega.Folding
