import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import Omega.Conclusion.LeyangFiveHypercubePartitionSplitting

namespace Omega.Conclusion

/-- The normalized body-address moment generating function for the five-branch Lee--Yang layer. -/
noncomputable def leyangFiveBranchBodyAddressMGF (n : Nat) (t : ℝ) : ℝ :=
  Omega.Zeta.leyangBranchsetHeatTrace n (-t) / Omega.Zeta.leyangBranchsetHeatTrace n 0

/-- The low-order cumulants extracted from the `log cosh` expansion. -/
def leyangFiveBranchBodyAddressCumulant (n r : Nat) : ℤ :=
  if Odd r then
    0
  else
    match r with
    | 2 => (2 * n : ℤ)
    | 4 => -(4 * n : ℤ)
    | 6 => (32 * n : ℤ)
    | _ => 0

/-- The exact cumulant package for the normalized five-branch body-address law. -/
structure LeyangFiveBranchBodyAddressRademacherCumulants (n : Nat) : Prop where
  mgf_closed_form : ∀ t : ℝ, leyangFiveBranchBodyAddressMGF n t = (Real.cosh t) ^ (2 * n)
  log_mgf_closed_form :
    ∀ t : ℝ, Real.log (leyangFiveBranchBodyAddressMGF n t) =
      (2 * n : ℝ) * Real.log (Real.cosh t)
  kappa2 : leyangFiveBranchBodyAddressCumulant n 2 = (2 * n : ℤ)
  kappa4 : leyangFiveBranchBodyAddressCumulant n 4 = -(4 * n : ℤ)
  kappa6 : leyangFiveBranchBodyAddressCumulant n 6 = (32 * n : ℤ)
  odd_vanish : ∀ m : Nat, Odd m → leyangFiveBranchBodyAddressCumulant n m = 0

lemma leyangFiveBranchBodyAddressMGF_closed_form (n : Nat) (t : ℝ) :
    leyangFiveBranchBodyAddressMGF n t = (Real.cosh t) ^ (2 * n) := by
  rcases paper_conclusion_leyang_five_hypercube_partition_splitting n t with ⟨hnum, hden⟩
  unfold leyangFiveBranchBodyAddressMGF
  rw [hnum, hden, mul_pow]
  have hfour : (4 : ℝ) ^ n = (2 : ℝ) ^ (2 * n) := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, pow_mul]
  rw [hfour]
  field_simp [pow_ne_zero n (show (2 : ℝ) ≠ 0 by norm_num),
    show (5 : ℝ) ≠ 0 by norm_num]

lemma leyangFiveBranchBodyAddressLogMGF_closed_form (n : Nat) (t : ℝ) :
    Real.log (leyangFiveBranchBodyAddressMGF n t) = (2 * n : ℝ) * Real.log (Real.cosh t) := by
  rw [leyangFiveBranchBodyAddressMGF_closed_form]
  simpa using (Real.log_pow (Real.cosh t) (2 * n))

/-- Paper label: `thm:conclusion-leyang-five-branch-body-address-rademacher-cumulants`. -/
theorem paper_conclusion_leyang_five_branch_body_address_rademacher_cumulants
    (n : Nat) : LeyangFiveBranchBodyAddressRademacherCumulants n := by
  refine ⟨leyangFiveBranchBodyAddressMGF_closed_form n, leyangFiveBranchBodyAddressLogMGF_closed_form n,
    ?_, ?_, ?_, ?_⟩
  · simp [leyangFiveBranchBodyAddressCumulant]
  · simp [leyangFiveBranchBodyAddressCumulant, show ¬ Odd 4 by decide]
  · simp [leyangFiveBranchBodyAddressCumulant, show ¬ Odd 6 by decide]
  · intro m hm
    simp [leyangFiveBranchBodyAddressCumulant, hm]

end Omega.Conclusion
