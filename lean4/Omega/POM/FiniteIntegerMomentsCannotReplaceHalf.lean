import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import Omega.POM.MomentCamouflageFiniteOrders

namespace Omega.POM

/-- Paper label: `thm:pom-finite-integer-moments-cannot-replace-half`.
If the finite-order camouflage identities hold up to some fixed integer cutoff `Q`, and the
half-order boost coming from the split atom is larger than the allowed heavy-block error, then the
integer moments still agree while the `q = 1/2` observable remains separated. -/
theorem paper_pom_finite_integer_moments_cannot_replace_half
    {Q M : ℕ} (a b : Fin Q → ℝ) {ε K : ℝ}
    (hQ : 2 ≤ Q)
    (hM : 1 ≤ M)
    (hε : 0 ≤ ε)
    (hmass : heavyPowerSum b 1 = heavyPowerSum a 1)
    (hmom : ∀ q : ℕ, 2 ≤ q → q ≤ Q →
      heavyPowerSum b q =
        heavyPowerSum a q + ε ^ q * (1 - (M : ℝ) ^ (1 - (q : ℝ))))
    (hsqrt : |heavyHalfOrder b - heavyHalfOrder a| ≤ K * ε ^ 2)
    (hsep : K * ε ^ 2 < |Real.sqrt ε * (Real.sqrt (M : ℝ) - 1)|) :
    (∀ q : ℕ, 1 ≤ q → q ≤ Q →
      camouflagePowerSum b ε M q = baselinePowerSum a ε q) ∧
      camouflageHalfOrder b ε M ≠ baselineHalfOrder a ε := by
  rcases
      paper_pom_moment_camouflage_finite_orders
        (Q := Q) (M := M) a b (ε := ε) (K := K) hQ hM hε hmass hmom hsqrt with
    ⟨hmatch, herr⟩
  refine ⟨hmatch, ?_⟩
  intro hEq
  have hcontr : |Real.sqrt ε * (Real.sqrt (M : ℝ) - 1)| ≤ K * ε ^ 2 := by
    simpa [hEq, abs_neg, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using herr
  exact (not_le_of_gt hsep) hcontr

end Omega.POM
