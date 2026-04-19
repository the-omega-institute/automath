import Mathlib.Tactic
import Omega.POM.MicrocanonicalAdaptiveNoGain

namespace Omega.POM

open scoped BigOperators

section

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Total microcanonical mass `N = Σ_x d(x)`. -/
def microcanonicalTotalMass (d : α → ℕ) : ℕ :=
  Finset.sum Finset.univ d

/-- Total mass carried by a finite set of types. -/
def microcanonicalSubsetMass (d : α → ℕ) (A : Finset α) : ℕ :=
  Finset.sum A d

/-- Probability that every type in `A` is absent after `t` without-replacement draws. -/
def microcanonicalSubsetAbsentProb (d : α → ℕ) (t : ℕ) (A : Finset α) : ℚ :=
  (Nat.choose (microcanonicalTotalMass d - microcanonicalSubsetMass d A) t : ℚ) /
    (Nat.choose (microcanonicalTotalMass d) t : ℚ)

/-- Inclusion-exclusion closed form for the cover-time tail. -/
def microcanonicalCoverTimeTailFormula (d : α → ℕ) (t : ℕ) : ℚ :=
  Finset.sum ((Finset.univ : Finset α).powerset.filter Finset.Nonempty) fun A =>
    (-1 : ℚ) ^ (A.card + 1) * microcanonicalSubsetAbsentProb d t A

/-- Chapter-local package for the microcanonical cover-time tail formula. The
without-replacement step law is inherited from
`paper_pom_microcanonical_adaptive_no_gain_without_replacement`; the remaining fields record the
subset-absence closed form and the finite inclusion-exclusion expansion. -/
structure MicrocanonicalCoverTimeTailData (d : α → ℕ) where
  subsetAbsentProb : ℕ → Finset α → ℚ
  coverTimeTailProb : ℕ → ℚ
  withoutReplacementStep :
    ∀ (N k : ℕ) (c : α → ℕ) (x : α), k < N →
      microcanonicalTrajectoryProb N (k + 1) d (incrementCount c x) =
        microcanonicalTrajectoryProb N k d c *
          ((((d x - c x : ℕ) : ℚ)) / (((N - k : ℕ) : ℚ)))
  subsetAbsentClosedForm :
    ∀ t A, A.Nonempty → subsetAbsentProb t A = microcanonicalSubsetAbsentProb d t A
  coverTimeTailInclusionExclusion :
    ∀ t,
      coverTimeTailProb t =
        Finset.sum ((Finset.univ : Finset α).powerset.filter Finset.Nonempty) fun A =>
          (-1 : ℚ) ^ (A.card + 1) * subsetAbsentProb t A

set_option maxHeartbeats 400000 in
/-- Paper-facing microcanonical cover-time tail formula: once the without-replacement subset
absence probabilities are identified, finite inclusion-exclusion gives the exact tail law.
    thm:pom-microcanonical-cover-time-tail-inclusion-exclusion -/
theorem paper_pom_microcanonical_cover_time_tail_inclusion_exclusion
    (d : α → ℕ) (h : MicrocanonicalCoverTimeTailData d) (t : ℕ) :
    h.coverTimeTailProb t = microcanonicalCoverTimeTailFormula d t := by
  classical
  rw [h.coverTimeTailInclusionExclusion t, microcanonicalCoverTimeTailFormula]
  refine Finset.sum_congr rfl ?_
  intro A hA
  rw [h.subsetAbsentClosedForm t A (Finset.mem_filter.mp hA).2]

end

end Omega.POM
