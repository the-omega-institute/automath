import Mathlib.Tactic
import Omega.Conclusion.EulerKroneckerSixphaseTransportLaw

namespace Omega.Conclusion

/-- The three-phase audit constant `σ_n` is the real version of the already-verified denominator
transport constant. -/
noncomputable def conclusion_euler_kronecker_lipschitz_threephase_audit_sigma (n : ℕ) : ℝ :=
  conclusion_euler_kronecker_threepoint_transport_spectrum_transport_constant n

/-- Concrete three-phase audit package extracted from the six-phase transport law. -/
def conclusion_euler_kronecker_lipschitz_threephase_audit_statement : Prop :=
  (∀ n : ℕ,
      n % 6 = 0 ∨ n % 6 = 2 →
      conclusion_euler_kronecker_lipschitz_threephase_audit_sigma n = 1 / 3) ∧
    (∀ n : ℕ,
      n % 6 = 1 ∨ n % 6 = 4 →
      conclusion_euler_kronecker_lipschitz_threephase_audit_sigma n = 1 / 2) ∧
    (∀ n : ℕ,
      n % 6 = 3 ∨ n % 6 = 5 →
      conclusion_euler_kronecker_lipschitz_threephase_audit_sigma n = 3 / 4) ∧
    (∀ n : ℕ, conclusion_euler_kronecker_lipschitz_threephase_audit_sigma n ≤ 3 / 4) ∧
    (∀ n : ℕ,
      n % 6 = 0 ∨ n % 6 = 2 →
      conclusion_euler_kronecker_lipschitz_threephase_audit_sigma n ≤ 1 / 3)

/-- Paper label: `thm:conclusion-euler-kronecker-lipschitz-threephase-audit`. -/
theorem paper_conclusion_euler_kronecker_lipschitz_threephase_audit :
    conclusion_euler_kronecker_lipschitz_threephase_audit_statement := by
  rcases paper_conclusion_euler_kronecker_sixphase_transport_law with ⟨h13, h12, h34⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n hn
    simpa [conclusion_euler_kronecker_lipschitz_threephase_audit_sigma] using
      congrArg (fun x : ℚ => (x : ℝ)) (h13 n hn)
  · intro n hn
    simpa [conclusion_euler_kronecker_lipschitz_threephase_audit_sigma] using
      congrArg (fun x : ℚ => (x : ℝ)) (h12 n hn)
  · intro n hn
    simpa [conclusion_euler_kronecker_lipschitz_threephase_audit_sigma] using
      congrArg (fun x : ℚ => (x : ℝ)) (h34 n hn)
  · intro n
    have hcases :
        n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 3 ∨ n % 6 = 4 ∨ n % 6 = 5 := by
      omega
    rcases hcases with h0 | h1 | h2 | h3 | h4 | h5
    · have hs :
          conclusion_euler_kronecker_lipschitz_threephase_audit_sigma n = (1 / 3 : ℝ) := by
          simpa [conclusion_euler_kronecker_lipschitz_threephase_audit_sigma] using
            congrArg (fun x : ℚ => (x : ℝ)) (h13 n (Or.inl h0))
      rw [hs]
      norm_num
    · have hs :
          conclusion_euler_kronecker_lipschitz_threephase_audit_sigma n = (1 / 2 : ℝ) := by
          simpa [conclusion_euler_kronecker_lipschitz_threephase_audit_sigma] using
            congrArg (fun x : ℚ => (x : ℝ)) (h12 n (Or.inl h1))
      rw [hs]
      norm_num
    · have hs :
          conclusion_euler_kronecker_lipschitz_threephase_audit_sigma n = (1 / 3 : ℝ) := by
          simpa [conclusion_euler_kronecker_lipschitz_threephase_audit_sigma] using
            congrArg (fun x : ℚ => (x : ℝ)) (h13 n (Or.inr h2))
      rw [hs]
      norm_num
    · have hs :
          conclusion_euler_kronecker_lipschitz_threephase_audit_sigma n = (3 / 4 : ℝ) := by
          simpa [conclusion_euler_kronecker_lipschitz_threephase_audit_sigma] using
            congrArg (fun x : ℚ => (x : ℝ)) (h34 n (Or.inl h3))
      rw [hs]
    · have hs :
          conclusion_euler_kronecker_lipschitz_threephase_audit_sigma n = (1 / 2 : ℝ) := by
          simpa [conclusion_euler_kronecker_lipschitz_threephase_audit_sigma] using
            congrArg (fun x : ℚ => (x : ℝ)) (h12 n (Or.inr h4))
      rw [hs]
      norm_num
    · have hs :
          conclusion_euler_kronecker_lipschitz_threephase_audit_sigma n = (3 / 4 : ℝ) := by
          simpa [conclusion_euler_kronecker_lipschitz_threephase_audit_sigma] using
            congrArg (fun x : ℚ => (x : ℝ)) (h34 n (Or.inr h5))
      rw [hs]
  · intro n hn
    have hsigma : conclusion_euler_kronecker_lipschitz_threephase_audit_sigma n = 1 / 3 := by
      simpa [conclusion_euler_kronecker_lipschitz_threephase_audit_sigma] using
        congrArg (fun x : ℚ => (x : ℝ)) (h13 n hn)
    rw [hsigma]

end Omega.Conclusion
