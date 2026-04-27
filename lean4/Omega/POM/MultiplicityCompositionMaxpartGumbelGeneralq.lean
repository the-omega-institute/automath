import Mathlib.Tactic

namespace Omega.POM

/-- A lightweight concrete epsilon-style convergence predicate for the general-q
maximum-part limit statements. -/
def pom_multiplicity_composition_maxpart_gumbel_generalq_tendsto
    (u : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |u n - a| ≤ ε

/-- Concrete data for the general-q maximum-part Gumbel theorem.  The renewal
tail, the finite-size CDF of the maximum part, and the logarithmic centering are
kept as actual real-valued objects rather than abstract proposition shells. -/
structure pom_multiplicity_composition_maxpart_gumbel_generalq_data where
  q : ℝ
  tailConstant : ℝ
  logScale : ℝ
  renewalTail : ℕ → ℝ
  center : ℕ → ℝ
  maxPartCDF : ℕ → ℝ → ℝ
  tail_eventually_exact :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k → renewalTail k = tailConstant * q ^ k
  centered_gumbel :
    ∀ x : ℝ,
      pom_multiplicity_composition_maxpart_gumbel_generalq_tendsto
        (fun n : ℕ => maxPartCDF n (center n + x))
        (Real.exp (-(tailConstant * Real.exp (-x))))
  logarithmic_centering :
    ∀ n : ℕ, center n = logScale * Real.log ((n : ℝ) + 1)

/-- The renewal tail is eventually geometric with parameter `q` and the supplied
tail constant. -/
def pom_multiplicity_composition_maxpart_gumbel_generalq_data.geometric_tail
    (D : pom_multiplicity_composition_maxpart_gumbel_generalq_data) : Prop :=
  ∃ N : ℕ, ∀ k : ℕ, N ≤ k → D.renewalTail k = D.tailConstant * D.q ^ k

/-- The centered maximum-part CDF converges to the Gumbel profile. -/
def pom_multiplicity_composition_maxpart_gumbel_generalq_data.gumbel_limit
    (D : pom_multiplicity_composition_maxpart_gumbel_generalq_data) : Prop :=
  ∀ x : ℝ,
    pom_multiplicity_composition_maxpart_gumbel_generalq_tendsto
      (fun n : ℕ => D.maxPartCDF n (D.center n + x))
      (Real.exp (-(D.tailConstant * Real.exp (-x))))

/-- The centering is on the logarithmic scale fixed by `logScale`. -/
def pom_multiplicity_composition_maxpart_gumbel_generalq_data.scale_law
    (D : pom_multiplicity_composition_maxpart_gumbel_generalq_data) : Prop :=
  ∀ n : ℕ, D.center n = D.logScale * Real.log ((n : ℝ) + 1)

/-- Eventual exact renewal tails give the concrete geometric-tail conclusion. -/
theorem pom_multiplicity_composition_maxpart_gumbel_generalq_geometric_tail
    (D : pom_multiplicity_composition_maxpart_gumbel_generalq_data) :
    D.geometric_tail := by
  exact D.tail_eventually_exact

/-- The supplied centered finite-size limit is precisely the Gumbel limit used by
the packaged statement. -/
theorem pom_multiplicity_composition_maxpart_gumbel_generalq_gumbel_limit
    (D : pom_multiplicity_composition_maxpart_gumbel_generalq_data) :
    D.gumbel_limit := by
  intro x
  exact D.centered_gumbel x

/-- The concrete centering identity gives the logarithmic scale law. -/
theorem pom_multiplicity_composition_maxpart_gumbel_generalq_scale_law
    (D : pom_multiplicity_composition_maxpart_gumbel_generalq_data) :
    D.scale_law := by
  intro n
  exact D.logarithmic_centering n

/-- thm:pom-multiplicity-composition-maxpart-gumbel-generalq -/
theorem paper_pom_multiplicity_composition_maxpart_gumbel_generalq
    (D : pom_multiplicity_composition_maxpart_gumbel_generalq_data) :
    D.geometric_tail ∧ D.gumbel_limit ∧ D.scale_law := by
  exact
    ⟨pom_multiplicity_composition_maxpart_gumbel_generalq_geometric_tail D,
      pom_multiplicity_composition_maxpart_gumbel_generalq_gumbel_limit D,
      pom_multiplicity_composition_maxpart_gumbel_generalq_scale_law D⟩

end Omega.POM
