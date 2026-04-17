import Mathlib.Tactic

namespace Omega.POM

/-- Resolution-reflector data for the KL Pythagoras identity on a resolution tower. The fields
record the reflected measures, the KL observable, and the certified regrouping of the KL
difference into a reflected KL term. -/
structure ResolutionReflectorData where
  Distrib : ℕ → Type
  reflect : ∀ {M : ℕ}, ℕ → Distrib M → Distrib M
  kl : ∀ {M : ℕ}, Distrib M → Distrib M → ℝ
  fiberLogRatioConstant :
    ∀ {M : ℕ} (m2 : ℕ) (_hm2 : m2 ≤ M) (_μ : Distrib M), Prop
  coarseFiberRegrouping :
    ∀ {M : ℕ} (m1 m2 : ℕ) (_hm2 : m2 ≤ M) (_hm1 : m1 ≤ m2) (_μ : Distrib M), Prop
  reflectedDifferenceAsKl :
    ∀ {M : ℕ} (m1 m2 : ℕ) (_hm2 : m2 ≤ M) (_hm1 : m1 ≤ m2) (μ : Distrib M),
      kl μ (reflect m1 μ) - kl μ (reflect m2 μ) =
        kl (reflect m2 μ) (reflect m1 μ)

/-- The regrouped KL difference on the finer reflector fiber is exactly the KL divergence between
the two reflected measures, which yields the tower Pythagoras identity by rearrangement.
    thm:pom-kl-pythagoras-tower -/
theorem paper_pom_kl_pythagoras_tower (R : ResolutionReflectorData) {M m1 m2 : ℕ}
    (hm2 : m2 ≤ M) (hm1 : m1 ≤ m2) (μ : R.Distrib M) :
    R.kl (M := M) μ (R.reflect m1 μ) =
      R.kl (M := M) μ (R.reflect m2 μ) +
        R.kl (M := M) (R.reflect m2 μ) (R.reflect m1 μ) := by
  have hDiff :
      R.kl (M := M) μ (R.reflect m1 μ) - R.kl (M := M) μ (R.reflect m2 μ) =
        R.kl (M := M) (R.reflect m2 μ) (R.reflect m1 μ) :=
    R.reflectedDifferenceAsKl (M := M) m1 m2 hm2 hm1 μ
  linarith

end Omega.POM
