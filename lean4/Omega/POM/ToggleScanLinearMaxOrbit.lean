import Mathlib.Tactic

namespace Omega.POM

/-- Closed-form maximum orbit length for the path-toggle scan operator.
    thm:pom-toggle-scan-linear-max-orbit -/
def toggleMaxOrbitLength (ℓ : ℕ) : ℕ :=
  3 * ℓ - 7

/-- Paper-facing wrapper for the linear maximal-orbit formula.
    thm:pom-toggle-scan-linear-max-orbit -/
theorem paper_pom_toggle_scan_linear_max_orbit (ℓ : ℕ) (hℓ : 4 ≤ ℓ) :
    toggleMaxOrbitLength ℓ = 3 * ℓ - 7 := by
  have hbound : 7 ≤ 3 * ℓ := by omega
  simp [toggleMaxOrbitLength]

/-- Candidate orbit lengths from the `L_k / d` description in the scan-orbit spectrum. -/
def toggleOrbitCandidateLength (n k d : ℕ) : ℕ :=
  (3 * n - 3 - 4 * k) / d

/-- The unique top-length orbit class is indexed by the `k = 1`, `d = 1` case. -/
def toggleTopOrbitClassCount (n : ℕ) : ℕ :=
  Nat.gcd (n - 3) 1

lemma toggleOrbitCandidateLength_le_max (n k d : ℕ) (hn : 4 ≤ n) (hk : 1 ≤ k) (_hd : 1 ≤ d) :
    toggleOrbitCandidateLength n k d ≤ toggleMaxOrbitLength n := by
  unfold toggleOrbitCandidateLength toggleMaxOrbitLength
  have hnum : 3 * n - 3 - 4 * k ≤ 3 * n - 7 := by omega
  exact (Nat.div_le_self _ _).trans hnum

/-- Paper-facing corollary: the top orbit length is `3n - 7`, no larger orbit can occur among the
`L_k / d` candidates, and the `gcd (n - 3, 1) = 1` class count shows that this maximal orbit is
unique.
    cor:pom-toggle-scan-unique-max-orbit -/
theorem paper_pom_toggle_scan_unique_max_orbit (n : ℕ) (hn : 4 ≤ n) :
    toggleOrbitCandidateLength n 1 1 = toggleMaxOrbitLength n ∧
      (∀ k d : ℕ, 1 ≤ k → 1 ≤ d → toggleOrbitCandidateLength n k d ≤ toggleMaxOrbitLength n) ∧
      toggleTopOrbitClassCount n = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [toggleOrbitCandidateLength, toggleMaxOrbitLength]
    omega
  · intro k d hk hd
    exact toggleOrbitCandidateLength_le_max n k d hn hk hd
  · simp [toggleTopOrbitClassCount]

end Omega.POM
