import Omega.SyncKernelWeighted.AbelMertensUniversal

namespace Omega.SyncKernelWeighted

noncomputable section

/-- The additive constant left after removing Euler's constant from the Mertens asymptotic. -/
def abel_mertens_constant_universal_abel_constant
    (D : SyncKernelAbelMertensAnalyticFamilyData) : ℝ :=
  D.mertensConstant - Real.eulerMascheroniConstant

/-- Paper-facing statement for the Abel/Mertens additive constant together with the finite-part
closed form and analyticity package. -/
def abel_mertens_constant_universal_statement
    (D : SyncKernelAbelMertensAnalyticFamilyData) : Prop :=
  (∀ N : ℕ, 1 ≤ N →
      D.partialSum N =
        Real.log N + (Real.eulerMascheroniConstant +
          abel_mertens_constant_universal_abel_constant D)) ∧
    D.finitePart = D.logC + ∑' k : ℕ, D.mobiusLogZeta (k + 2) ∧
    D.finitePartAnalytic

/-- Paper label: `cor:abel-mertens-constant-universal`. -/
def paper_abel_mertens_constant_universal
    (D : Omega.SyncKernelWeighted.SyncKernelAbelMertensAnalyticFamilyData) : Prop :=
  abel_mertens_constant_universal_statement D

theorem abel_mertens_constant_universal_certified
    (D : SyncKernelAbelMertensAnalyticFamilyData) :
    paper_abel_mertens_constant_universal D := by
  rcases paper_abel_mertens_universal D with ⟨_, hmertens, hfinite, hanalytic⟩
  refine ⟨?_, hfinite, hanalytic⟩
  intro N hN
  calc
    D.partialSum N = Real.log N + D.mertensConstant := hmertens N hN
    _ =
        Real.log N + (Real.eulerMascheroniConstant +
          abel_mertens_constant_universal_abel_constant D) := by
            unfold abel_mertens_constant_universal_abel_constant
            rw [sub_eq_add_neg]
            congr 1
            calc
              D.mertensConstant =
                  D.mertensConstant +
                    (Real.eulerMascheroniConstant + (-Real.eulerMascheroniConstant)) := by
                      simp
              _ = (D.mertensConstant + Real.eulerMascheroniConstant) +
                    (-Real.eulerMascheroniConstant) := by rw [add_assoc]
              _ = (Real.eulerMascheroniConstant + D.mertensConstant) +
                    (-Real.eulerMascheroniConstant) := by
                      rw [add_comm D.mertensConstant Real.eulerMascheroniConstant]
              _ = Real.eulerMascheroniConstant + (D.mertensConstant + -Real.eulerMascheroniConstant) := by
                    rw [← add_assoc]

end

end Omega.SyncKernelWeighted
