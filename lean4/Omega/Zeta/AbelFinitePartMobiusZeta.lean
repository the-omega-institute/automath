import Mathlib

namespace Omega.Zeta

noncomputable section

/-- Concrete finite-part package for the Abelian Möbius-zeta decomposition. The `k = 1` term is
the simple-pole residue, and the finite part keeps the unchanged absolutely convergent tail
starting at `k = 2`. -/
structure AbelFinitePartMobiusZetaData where
  finitePart : ℝ
  logC : ℝ
  mobiusLogZeta : ℕ → ℝ
  hResidue : mobiusLogZeta 1 = logC
  hFinitePartSplit : finitePart = mobiusLogZeta 1 + ∑' k : ℕ, mobiusLogZeta (k + 2)
  hTailSummable : Summable (fun k : ℕ => mobiusLogZeta (k + 2))

namespace AbelFinitePartMobiusZetaData

/-- Closed form obtained by separating the `k = 1` pole term from the convergent Möbius tail. -/
def finitePartClosedForm (D : AbelFinitePartMobiusZetaData) : Prop :=
  D.finitePart = D.logC + ∑' k : ℕ, D.mobiusLogZeta (k + 2)

end AbelFinitePartMobiusZetaData

open AbelFinitePartMobiusZetaData

/-- Publication-facing finite-part closed form for the Abelian Möbius-zeta decomposition.
    prop:abel-finite-part-mobius-zeta -/
theorem paper_etds_abel_finite_part_mobius_zeta (D : AbelFinitePartMobiusZetaData) :
    D.finitePartClosedForm := by
  rw [AbelFinitePartMobiusZetaData.finitePartClosedForm]
  calc
    D.finitePart = D.mobiusLogZeta 1 + ∑' k : ℕ, D.mobiusLogZeta (k + 2) := D.hFinitePartSplit
    _ = D.logC + ∑' k : ℕ, D.mobiusLogZeta (k + 2) := by rw [D.hResidue]

end
end Omega.Zeta
