import Mathlib.Tactic
import Omega.Folding.FiberArithmetic
import Omega.Folding.FoldbinTailcountBoundFromS2
import Omega.Folding.MomentSum
import Omega.GU.Window6FoldbinGaugeLowDegreeHomology

namespace Omega.Folding

noncomputable section

/-- The window-`6` multiplicity profile used in the moment certificate. -/
noncomputable def foldbin_central_2extension_moment_certificate_multiplicity : X 6 → ℕ :=
  fun x => X.fiberMultiplicity x

/-- The paper's `A_m` bound specialized to the audited window `6`. -/
noncomputable def foldbin_central_2extension_moment_certificate_A_m : ℕ :=
  (momentSum 2 6 - Fintype.card (X 6)) / 3

/-- The paper's `B_m` bound specialized to the audited window `6`. -/
noncomputable def foldbin_central_2extension_moment_certificate_B_m : ℕ :=
  (momentSum 2 6 - Fintype.card (X 6)) / 15

/-- Window-`6` version of the central `2`-extension moment certificate. -/
def foldbin_central_2extension_moment_certificate_statement
    (D : Omega.GU.Window6FoldbinGaugeLowDegreeHomologyData) : Prop :=
  foldBinTailCount foldbin_central_2extension_moment_certificate_multiplicity 1 ≤
      foldbin_central_2extension_moment_certificate_A_m ∧
    foldBinTailCount foldbin_central_2extension_moment_certificate_multiplicity 3 ≤
      foldbin_central_2extension_moment_certificate_B_m ∧
    D.n2 ≤ foldbin_central_2extension_moment_certificate_A_m ∧
    D.n4 ≤ foldbin_central_2extension_moment_certificate_B_m ∧
    D.h2Rank ≤
      foldbin_central_2extension_moment_certificate_B_m +
        Nat.choose foldbin_central_2extension_moment_certificate_A_m 2 ∧
    2 ^ D.h2CohomologyRank ≤
      2 ^ (foldbin_central_2extension_moment_certificate_B_m +
        Nat.choose (foldbin_central_2extension_moment_certificate_A_m + 1) 2)

/-- Paper label: `cor:foldbin-central-2extension-moment-certificate`. The tailcount bound from the
quadratic moment is instantiated at thresholds `2` and `4`; the audited window-`6` homology
closed forms then give the advertised upper bounds for `H₂` and `H²`. -/
theorem paper_foldbin_central_2extension_moment_certificate
    (D : Omega.GU.Window6FoldbinGaugeLowDegreeHomologyData) :
    foldbin_central_2extension_moment_certificate_statement D := by
  have hpos : ∀ x : X 6, 1 ≤ foldbin_central_2extension_moment_certificate_multiplicity x := by
    intro x
    exact Nat.succ_le_of_lt (X.fiberMultiplicity_pos x)
  have htail2 :
      foldBinTailCount foldbin_central_2extension_moment_certificate_multiplicity 1 ≤
        foldbin_central_2extension_moment_certificate_A_m := by
    simpa [foldbin_central_2extension_moment_certificate_multiplicity,
      foldbin_central_2extension_moment_certificate_A_m, momentSum] using
      (paper_foldbin_tailcount_bound_from_s2
        (α := X 6) foldbin_central_2extension_moment_certificate_multiplicity 2
        (by decide) hpos)
  have htail4 :
      foldBinTailCount foldbin_central_2extension_moment_certificate_multiplicity 3 ≤
        foldbin_central_2extension_moment_certificate_B_m := by
    simpa [foldbin_central_2extension_moment_certificate_multiplicity,
      foldbin_central_2extension_moment_certificate_B_m, momentSum] using
      (paper_foldbin_tailcount_bound_from_s2
        (α := X 6) foldbin_central_2extension_moment_certificate_multiplicity 4
        (by decide) hpos)
  have hA :
      foldbin_central_2extension_moment_certificate_A_m = 66 := by
    rw [foldbin_central_2extension_moment_certificate_A_m, momentSum_two_six, X.card_X_six]
  have hB :
      foldbin_central_2extension_moment_certificate_B_m = 13 := by
    rw [foldbin_central_2extension_moment_certificate_B_m, momentSum_two_six, X.card_X_six]
  have hn2 : D.n2 = 19 := D.n2_eq
  have hn4 : D.n4 = 7 := D.n4_eq
  have hh2 : D.h2Rank = 178 := by
    simpa [Omega.GU.Window6FoldbinGaugeLowDegreeHomologyData.h2ClosedForm] using D.h2ClosedForm_true
  have hh2coh : D.h2CohomologyRank = 197 := by
    simpa [Omega.GU.Window6FoldbinGaugeLowDegreeHomologyData.h2CohomologyClosedForm] using
      D.h2CohomologyClosedForm_true
  refine ⟨htail2, htail4, ?_, ?_, ?_, ?_⟩
  · rw [hn2, hA]
    omega
  · rw [hn4, hB]
    omega
  · rw [hh2, hA, hB]
    native_decide
  · apply Nat.pow_le_pow_right (by decide : 0 < 2)
    rw [hh2coh, hA, hB]
    native_decide

end

end Omega.Folding
