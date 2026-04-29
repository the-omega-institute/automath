import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-sublinear-toeplitz-audit-impossible`. -/
theorem paper_conclusion_sublinear_toeplitz_audit_impossible (audit detect lower : ℕ → ℝ)
    (complete : Prop)
    (hcomplete : complete → ∃ N, ∀ n ≥ N, detect n ≤ audit n)
    (hlower : ∃ N, ∀ n ≥ N, lower n ≤ detect n)
    (hsub : ∃ N, ∀ n ≥ N, audit n < lower n) :
    ¬ complete := by
  intro hcomplete_true
  rcases hcomplete hcomplete_true with ⟨Ncomplete, hcomplete_eventual⟩
  rcases hlower with ⟨Nlower, hlower_eventual⟩
  rcases hsub with ⟨Nsub, hsub_eventual⟩
  let N := max Ncomplete (max Nlower Nsub)
  have hNcomplete : Ncomplete ≤ N := Nat.le_max_left _ _
  have hNlower : Nlower ≤ N :=
    le_trans (Nat.le_max_left Nlower Nsub) (Nat.le_max_right Ncomplete (max Nlower Nsub))
  have hNsub : Nsub ≤ N :=
    le_trans (Nat.le_max_right Nlower Nsub) (Nat.le_max_right Ncomplete (max Nlower Nsub))
  have hdetect_audit : detect N ≤ audit N := hcomplete_eventual N hNcomplete
  have hlower_detect : lower N ≤ detect N := hlower_eventual N hNlower
  have haudit_lower : audit N < lower N := hsub_eventual N hNsub
  linarith

end Omega.Conclusion
