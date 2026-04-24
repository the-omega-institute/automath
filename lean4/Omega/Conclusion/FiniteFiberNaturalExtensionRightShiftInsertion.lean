import Omega.Folding.KilloNaturalExtensionBranchRegister

namespace Omega.Conclusion

/-- `thm:conclusion-finite-fiber-natural-extension-right-shift-insertion` -/
theorem paper_conclusion_finite_fiber_natural_extension_right_shift_insertion {X : Type*}
    (T : X → X) (beta : X → Nat) (decode : X → Nat → X) (hT : ∀ y a, T (decode y a) = y)
    (hβ : ∀ y a, beta (decode y a) = a) (hdecode : ∀ x, decode (T x) (beta x) = x) :
    Function.Bijective (Omega.Folding.branchRegisterCodeToImage T beta) ∧
      Function.LeftInverse (Omega.Folding.branchRegisterDecodeImage T beta decode hT)
        (Omega.Folding.branchRegisterCodeToImage T beta) ∧
      Function.RightInverse (Omega.Folding.branchRegisterDecodeImage T beta decode hT)
        (Omega.Folding.branchRegisterCodeToImage T beta) ∧
      ∀ s : Omega.Folding.NaturalExtension T,
        Omega.Folding.branchRegisterShift T beta (Omega.Folding.branchRegisterCodeToImage T beta s)
          = Omega.Folding.branchRegisterCodeToImage T beta
              (Omega.Folding.naturalExtensionShift T s) := by
  simpa using
    Omega.Folding.paper_killo_natural_extension_branch_register T beta decode hT hβ hdecode

end Omega.Conclusion
