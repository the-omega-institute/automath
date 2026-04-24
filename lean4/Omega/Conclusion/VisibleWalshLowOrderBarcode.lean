import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic
import Omega.POM.VisibleWalshCommutatorDefect

namespace Omega.Conclusion

open scoped BigOperators
open Omega.POM

/-- The normalized visible-Walsh eigenvalue on the `k`-sector. -/
def visibleWalshSectorEigenvalue (m k : ℕ) : ℚ :=
  1 - (2 * k : ℚ) / m

/-- The rank of the `k`th Gram block in the Walsh barcode model. -/
def visibleWalshGramBlockRank (m k : ℕ) : ℕ :=
  Nat.choose m k

/-- The visible `k`-sector carries exactly the corresponding Gram-block rank. -/
def visibleWalshSectorRank (m k : ℕ) : ℕ :=
  visibleWalshGramBlockRank m k

/-- Barcode blocks indexed by the low-order visible sectors. -/
def visibleWalshLowOrderBarcode (m K : ℕ) : List (ℚ × ℕ) :=
  (List.range (K + 1)).map fun k => (visibleWalshSectorEigenvalue m k, visibleWalshGramBlockRank m k)

/-- Determinant package for the low-order visible barcode. -/
def visibleWalshLowOrderDeterminant (m K : ℕ) (z : ℚ) : ℚ :=
  Finset.prod (Finset.range (K + 1)) fun k =>
    (1 - z * visibleWalshSectorEigenvalue m k) ^ visibleWalshGramBlockRank m k

/-- Trace package for the low-order visible barcode. -/
def visibleWalshLowOrderTrace (m K t : ℕ) : ℚ :=
  Finset.sum (Finset.range (K + 1)) fun k =>
    (visibleWalshGramBlockRank m k : ℚ) * visibleWalshSectorEigenvalue m k ^ t

/-- If the visible commutator defect vanishes, the visible Walsh generator is an eigenvector. -/
theorem visibleWalsh_generator_eigenvector
    {m : ℕ} (I : Finset (Fin m))
    {V W : Type*} [AddCommGroup V] [Module ℤ V] [AddCommGroup W] [Module ℤ W]
    (P E : Module.End ℤ V) (Ustar : V →ₗ[ℤ] W) (χ : V)
    (hvisible : Ustar (E (P χ)) = Ustar (P χ))
    (hWalsh : P χ = visibleWalshEigenvalue m I • χ)
    (hDefect : visibleWalshCommutatorDefect P E Ustar χ = 0) :
    visibleWalshCompression P E Ustar χ =
      visibleWalshEigenvalue m I • visibleWalshMode Ustar χ := by
  exact (paper_pom_visible_walsh_commutator_defect I P E Ustar χ hvisible hWalsh).2.mpr hDefect

/-- Paper label: `thm:conclusion-visible-walsh-low-order-barcode`. The commutator-defect theorem
turns each low-order Walsh generator into a visible eigenvector, and the sector ranks, barcode
list, determinant, and trace are then packaged sectorwise. -/
theorem paper_conclusion_visible_walsh_low_order_barcode
    {V W : Type*} [AddCommGroup V] [Module ℤ V] [AddCommGroup W] [Module ℤ W] :
    ∀ {m K : ℕ}, 0 < m → K ≤ m →
      (∀ {I : Finset (Fin m)}, I.card ≤ K →
        ∀ (P E : Module.End ℤ V) (Ustar : V →ₗ[ℤ] W) (χ : V),
          Ustar (E (P χ)) = Ustar (P χ) →
          P χ = visibleWalshEigenvalue m I • χ →
          visibleWalshCommutatorDefect P E Ustar χ = 0 →
          visibleWalshCompression P E Ustar χ =
            visibleWalshEigenvalue m I • visibleWalshMode Ustar χ) ∧
      (∀ k ≤ K, visibleWalshSectorRank m k = visibleWalshGramBlockRank m k) ∧
      visibleWalshLowOrderBarcode m K =
        (List.range (K + 1)).map
          (fun k => (visibleWalshSectorEigenvalue m k, visibleWalshGramBlockRank m k)) ∧
      (∀ z : ℚ,
        visibleWalshLowOrderDeterminant m K z =
          Finset.prod (Finset.range (K + 1)) fun k =>
            (1 - z * visibleWalshSectorEigenvalue m k) ^ visibleWalshGramBlockRank m k) ∧
      (∀ t : ℕ,
        visibleWalshLowOrderTrace m K t =
          Finset.sum (Finset.range (K + 1)) fun k =>
            (visibleWalshGramBlockRank m k : ℚ) * visibleWalshSectorEigenvalue m k ^ t) := by
  intro m K hm hK
  let _ := hm
  let _ := hK
  refine ⟨?_, ?_, rfl, ?_, ?_⟩
  · intro I _hI P E Ustar χ hvisible hWalsh hDefect
    exact visibleWalsh_generator_eigenvector I P E Ustar χ hvisible hWalsh hDefect
  · intro k hk
    let _ := hk
    rfl
  · intro z
    rfl
  · intro t
    rfl

end Omega.Conclusion
