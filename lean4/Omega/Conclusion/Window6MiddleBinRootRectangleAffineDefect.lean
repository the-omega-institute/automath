import Mathlib.Tactic
import Omega.Folding.BinFold

namespace Omega.Conclusion

attribute [local instance] Omega.fintypeX

/-- Paper label: `thm:conclusion-window6-middle-bin-root-rectangle-affine-defect`. -/
theorem paper_conclusion_window6_middle_bin_root_rectangle_affine_defect :
    ({Omega.X.ofNat 6 9, Omega.X.ofNat 6 10, Omega.X.ofNat 6 11, Omega.X.ofNat 6 12} :
        Finset (Omega.X 6)).card = 4 ∧
      (∀ x : Omega.X 6,
        x ∈ ({Omega.X.ofNat 6 9, Omega.X.ofNat 6 10, Omega.X.ofNat 6 11,
              Omega.X.ofNat 6 12} : Finset (Omega.X 6)) ↔
          Omega.cBinFiberMult 6 x = 3) ∧
      (∀ x : Omega.X 6,
        x ∈ ({Omega.X.ofNat 6 9, Omega.X.ofNat 6 10, Omega.X.ofNat 6 11,
              Omega.X.ofNat 6 12} : Finset (Omega.X 6)) →
          ((Finset.range 64).filter (fun n => Omega.cBinFold 6 n = x)).card = 3) := by
  native_decide

end Omega.Conclusion
