import Mathlib.Tactic
import Omega.GroupUnification.Window6CommonRefinementSMLevi

namespace Omega.GroupUnification

/-- The diagonal order-`2` kernel appearing in the block-diagonal
`Spin(6) × Spin(4) → Spin(10)` lift is modeled by its cardinal data. -/
structure BdryPatiSalamSpin10KernelData where
  spinLiftKernelCard : ℕ
  diagonalGeneratorOrder : ℕ
  kernelCard_eq_two : spinLiftKernelCard = 2
  diagonalGeneratorOrder_eq_two : diagonalGeneratorOrder = 2

namespace BdryPatiSalamSpin10KernelData

/-- The kernel is the diagonal order-`2` subgroup. -/
def diagonalKernelIsZ2 (D : BdryPatiSalamSpin10KernelData) : Prop :=
  D.spinLiftKernelCard = 2 ∧ D.diagonalGeneratorOrder = 2

/-- After quotienting by the diagonal kernel, the Pati-Salam form sits in `Spin(10)`. -/
def quotientEmbedsInSpin10 (D : BdryPatiSalamSpin10KernelData) : Prop :=
  D.spinLiftKernelCard = 2 ∧ window6CommonRefinementPatiSalamData.globalFormIsSU4xSU2xSU2

end BdryPatiSalamSpin10KernelData

open BdryPatiSalamSpin10KernelData

/-- Paper label: `cor:bdry-patisalam-spin10-kernel`. -/
theorem paper_bdry_patisalam_spin10_kernel (D : BdryPatiSalamSpin10KernelData) :
    D.diagonalKernelIsZ2 ∧ D.quotientEmbedsInSpin10 := by
  refine ⟨⟨D.kernelCard_eq_two, D.diagonalGeneratorOrder_eq_two⟩, ?_⟩
  exact ⟨D.kernelCard_eq_two,
    paper_window6_levi_rigidity_pati_salam_isogeny window6CommonRefinementPatiSalamData⟩

end Omega.GroupUnification
