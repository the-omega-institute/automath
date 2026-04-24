import Mathlib

namespace Omega.GU

open Matrix

/-- Reduction of an integral matrix modulo `p`. -/
def modpMatrixReduction {n p : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    Matrix (Fin n) (Fin n) (ZMod p) :=
  A.map (Int.castRingHom (ZMod p))

/-- The `𝔽_p`-span of the reduced integral lattice witnesses. -/
def modpReductionSpan {n p r : ℕ} (lattice : Fin r → Matrix (Fin n) (Fin n) ℤ) :
    Submodule (ZMod p) (Matrix (Fin n) (Fin n) (ZMod p)) :=
  Submodule.span (ZMod p) (Set.range fun i : Fin r => modpMatrixReduction (p := p) (lattice i))

/-- The `𝔽_p`-span of the reduced Lie words appearing in the mod-`p` certificate. -/
def modpLieWordSpan {n p : ℕ} {ι : Type*} (words : ι → Matrix (Fin n) (Fin n) (ZMod p)) :
    Submodule (ZMod p) (Matrix (Fin n) (Fin n) (ZMod p)) :=
  Submodule.span (ZMod p) (Set.range words)

/-- If every mod-`p` Lie word is the reduction of an integral lattice element, then the mod-`p`
span dimension is bounded by the number of integral lattice witnesses. This is the finite-
dimensional lift used to transfer a full-rank mod-`p` certificate to the characteristic-`0`
window-`6` Lie-envelope arguments.
    `lem:modp-lie-dimension-upperbound` -/
theorem paper_modp_lie_dimension_upperbound
    {n p r : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι]
    (lattice : Fin r → Matrix (Fin n) (Fin n) ℤ)
    (words : ι → Matrix (Fin n) (Fin n) (ZMod p))
    (hlift : ∀ i, words i ∈ modpReductionSpan (p := p) lattice) :
    Module.finrank (ZMod p) (modpLieWordSpan (p := p) words) ≤ r := by
  have hspan :
      modpLieWordSpan (p := p) words ≤ modpReductionSpan (p := p) lattice := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact hlift i
  calc
    Module.finrank (ZMod p) (modpLieWordSpan (p := p) words) ≤
        Module.finrank (ZMod p) (modpReductionSpan (p := p) lattice) :=
      Submodule.finrank_mono hspan
    _ ≤ (Set.range fun i : Fin r => modpMatrixReduction (p := p) (lattice i)).toFinset.card := by
      unfold modpReductionSpan
      simpa using
        (finrank_span_le_card (R := ZMod p)
          (s := Set.range fun i : Fin r => modpMatrixReduction (p := p) (lattice i)))
    _ ≤ Fintype.card (Fin r) := by
      simpa [Set.toFinset_range] using
        (Finset.card_image_le
          (s := (Finset.univ : Finset (Fin r)))
          (f := fun i : Fin r => modpMatrixReduction (p := p) (lattice i)))
    _ = r := by simp

end Omega.GU
