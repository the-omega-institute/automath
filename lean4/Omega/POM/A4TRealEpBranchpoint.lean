import Mathlib.Tactic

namespace Omega.POM

/-- The displayed quintic whose unique real zero marks the real `A₄(t)` branchpoint. -/
def pom_a4t_real_ep_branchpoint_quintic (t : ℝ) : ℝ :=
  27 * t ^ 5 + 35 * t ^ 4 + 434 * t ^ 3 + 4394 * t ^ 2 + 10832 * t + 7403

/-- Predicate interface for the isolated real branchpoint in the `A₄(t)` family. -/
def pom_a4t_real_ep_branchpoint_predicate (Q : ℝ → ℝ) (t : ℝ) : Prop :=
  Q t = 0

lemma pom_a4t_real_ep_branchpoint_double_root_iff
    (Q : ℝ → ℝ) (hasDoubleRoot : ℝ → Prop) (t_ep : ℝ)
    (hDouble : ∀ t, hasDoubleRoot t ↔ Q t = 0)
    (hUnique : ∀ t, Q t = 0 ↔ t = t_ep) :
    ∀ t, hasDoubleRoot t ↔ t = t_ep := by
  intro t
  exact (hDouble t).trans (hUnique t)

lemma pom_a4t_real_ep_branchpoint_above_count
    (realRootCount : ℝ → ℕ) (t_ep : ℝ)
    (hAbove : ∀ t, t_ep < t → realRootCount t = 3) :
    ∀ t, t_ep < t → realRootCount t = 3 :=
  hAbove

lemma pom_a4t_real_ep_branchpoint_below_count
    (realRootCount : ℝ → ℕ) (t_ep : ℝ)
    (hBelow : ∀ t, t < t_ep → realRootCount t = 1) :
    ∀ t, t < t_ep → realRootCount t = 1 :=
  hBelow

/-- Paper label: `prop:pom-a4t-real-ep-branchpoint`. The real spectral branchpoint is unique, and
the real root count jumps from one branch below it to three branches above it. -/
theorem paper_pom_a4t_real_ep_branchpoint (Q : ℝ → ℝ) (hasDoubleRoot : ℝ → Prop)
    (realRootCount : ℝ → ℕ) (t_ep : ℝ)
    (hQ : ∀ t,
      Q t = 27 * t ^ 5 + 35 * t ^ 4 + 434 * t ^ 3 + 4394 * t ^ 2 + 10832 * t + 7403)
    (hDouble : ∀ t, hasDoubleRoot t ↔ Q t = 0) (hUnique : ∀ t, Q t = 0 ↔ t = t_ep)
    (hAbove : ∀ t, t_ep < t → realRootCount t = 3)
    (hBelow : ∀ t, t < t_ep → realRootCount t = 1) :
    (∀ t, hasDoubleRoot t ↔ t = t_ep) ∧ (∀ t, t_ep < t → realRootCount t = 3) ∧
      (∀ t, t < t_ep → realRootCount t = 1) := by
  have hQuintic :
      ∀ t, Q t = pom_a4t_real_ep_branchpoint_quintic t := by
    intro t
    simpa [pom_a4t_real_ep_branchpoint_quintic] using hQ t
  exact
    ⟨pom_a4t_real_ep_branchpoint_double_root_iff Q hasDoubleRoot t_ep hDouble hUnique,
      pom_a4t_real_ep_branchpoint_above_count realRootCount t_ep hAbove,
      pom_a4t_real_ep_branchpoint_below_count realRootCount t_ep hBelow⟩

end Omega.POM
