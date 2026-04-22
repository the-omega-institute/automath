import Mathlib.Tactic
import Omega.Conclusion.CoordinateBundleKernelSlabDecomposition
import Omega.Conclusion.ScreenRelativeBettiRenyiFlatness
import Omega.Conclusion.ScreenZeroErrorAuditTime
import Omega.SPG.CoordinateBundleScreenCount

namespace Omega.Conclusion

open Omega.SPG.CoordinateBundleScreenCount

/-- Concrete exact-area-law statement for the internal coordinate bundle screen. -/
def conclusion_coordinate_bundle_exact_area_law_statement (m n s : ℕ) : Prop :=
  let β := 2 ^ (m * (n - s))
  let D : ScreenFlatFiberData := { totalBits := m * n, beta := β }
  screenComponentCount m n s - 1 = β ∧
    D.shannonCond = β ∧
    (∀ q : Nat, D.renyiCond q = β) ∧
    D.renyiInf = β ∧
    (∃ T : Nat, T = β ∧ 2 ^ T >= 2 ^ β ∧ ∀ t < T, 2 ^ t < 2 ^ β) ∧
    auditCost m n s = β

lemma conclusion_coordinate_bundle_exact_area_law_binary_zeroerror_time_exact (β : Nat) :
    ∃ T : Nat, T = β ∧ 2 ^ T >= 2 ^ β ∧ ∀ t < T, 2 ^ t < 2 ^ β := by
  rcases paper_conclusion_screen_zeroerror_audit_time 2 β (by norm_num) with ⟨T, hT, hmin⟩
  have hTle : T ≤ β := by
    by_contra hTle
    have hβlt : β < T := Nat.lt_of_not_ge hTle
    exact (Nat.lt_irrefl (2 ^ β)) ((hmin β hβlt).trans_le (by simpa using hT))
  have hβle : β ≤ T := by
    by_contra hβle
    have hTlt : T < β := Nat.lt_of_not_ge hβle
    exact (not_lt_of_ge hT) (Nat.pow_lt_pow_right (by decide : 1 < 2) hTlt)
  have hEq : T = β := le_antisymm hTle hβle
  exact ⟨T, hEq, hT, hmin⟩

/-- Paper label: `cor:conclusion-coordinate-bundle-exact-area-law`. -/
theorem paper_conclusion_coordinate_bundle_exact_area_law (m n s : ℕ) :
    conclusion_coordinate_bundle_exact_area_law_statement m n s := by
  dsimp [conclusion_coordinate_bundle_exact_area_law_statement]
  let β := 2 ^ (m * (n - s))
  let D : ScreenFlatFiberData := { totalBits := m * n, beta := β }
  have hKernel :
      screenComponentCount m n s - 1 = β := by
    simpa [β] using paper_conclusion_coordinate_bundle_kernel_slab_decomposition m n s
  have hFlat := paper_conclusion_relative_betti_renyi_flatness D
  have hTime :
      ∃ T : Nat, T = β ∧ 2 ^ T >= 2 ^ β ∧ ∀ t < T, 2 ^ t < 2 ^ β :=
    conclusion_coordinate_bundle_exact_area_law_binary_zeroerror_time_exact β
  have hCost : auditCost m n s = β := by
    simpa [β] using (paper_spg_internal_coordinate_bundle_screen_cost_closed_form m n s).2
  rcases hFlat with ⟨hShannon, _, _, hRenyi, hRenyiInf⟩
  exact ⟨hKernel, hShannon, hRenyi, hRenyiInf, hTime, hCost⟩

end Omega.Conclusion
