import Mathlib.Tactic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-zero-mean-residue-basis-independent-tomography`. -/
theorem paper_conclusion_zero_mean_residue_basis_independent_tomography {n : ℕ}
    (B Binv : Matrix (Fin n) (Fin n) ℂ) (L c : Fin n → ℂ) (hL : B.mulVec c = L)
    (hLeft : ∀ v : Fin n → ℂ, Binv.mulVec (B.mulVec v) = v) :
    Binv.mulVec L = c := by
  rw [← hL]
  exact hLeft c

end Omega.Conclusion
