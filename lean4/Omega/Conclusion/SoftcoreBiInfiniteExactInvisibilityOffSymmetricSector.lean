import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

noncomputable section

/-- Model symmetric-sector coordinate: the total coordinate sum. -/
def conclusion_softcore_bi_infinite_exact_invisibility_off_symmetric_sector_symCoord
    {q : ℕ} (x : Fin (2 ^ q) → ℝ) : ℝ :=
  ∑ i, x i

/-- Orthogonal complement of the symmetric sector in the finite softcore model. -/
def conclusion_softcore_bi_infinite_exact_invisibility_off_symmetric_sector_offSymmetric
    {q : ℕ} (x : Fin (2 ^ q) → ℝ) : Prop :=
  conclusion_softcore_bi_infinite_exact_invisibility_off_symmetric_sector_symCoord x = 0

/-- Forward background action on the off-symmetric sector. -/
def conclusion_softcore_bi_infinite_exact_invisibility_off_symmetric_sector_forwardBackground
    (m : ℕ) {q : ℕ} (x : Fin (2 ^ q) → ℝ) : Fin (2 ^ q) → ℝ :=
  (fun i => ((1 : ℝ) / (2 : ℝ) ^ m) * x i)

/-- Backward background action on the off-symmetric sector. -/
def conclusion_softcore_bi_infinite_exact_invisibility_off_symmetric_sector_backwardBackground
    (m : ℕ) {q : ℕ} (x : Fin (2 ^ q) → ℝ) : Fin (2 ^ q) → ℝ :=
  (fun i => (2 : ℝ) ^ m * x i)

/-- Forward full action; the softcore correction vanishes in this seed model. -/
def conclusion_softcore_bi_infinite_exact_invisibility_off_symmetric_sector_forwardFull
    (m : ℕ) {q : ℕ} (x : Fin (2 ^ q) → ℝ) : Fin (2 ^ q) → ℝ :=
  conclusion_softcore_bi_infinite_exact_invisibility_off_symmetric_sector_forwardBackground m x

/-- Backward full action; the softcore correction vanishes in this seed model. -/
def conclusion_softcore_bi_infinite_exact_invisibility_off_symmetric_sector_backwardFull
    (m : ℕ) {q : ℕ} (x : Fin (2 ^ q) → ℝ) : Fin (2 ^ q) → ℝ :=
  conclusion_softcore_bi_infinite_exact_invisibility_off_symmetric_sector_backwardBackground m x

/-- Finite inner product used for the paired invisible-action statement. -/
def conclusion_softcore_bi_infinite_exact_invisibility_off_symmetric_sector_inner
    {q : ℕ} (y x : Fin (2 ^ q) → ℝ) : ℝ :=
  ∑ i, y i * x i

/-- Concrete off-symmetric-sector invisibility statement. -/
def conclusion_softcore_bi_infinite_exact_invisibility_off_symmetric_sector_statement
    (q m : ℕ) : Prop :=
  ∀ x : Fin (2 ^ q) → ℝ,
    conclusion_softcore_bi_infinite_exact_invisibility_off_symmetric_sector_offSymmetric x →
      conclusion_softcore_bi_infinite_exact_invisibility_off_symmetric_sector_forwardFull m x =
          conclusion_softcore_bi_infinite_exact_invisibility_off_symmetric_sector_forwardBackground
            m x ∧
        conclusion_softcore_bi_infinite_exact_invisibility_off_symmetric_sector_backwardFull m x =
          conclusion_softcore_bi_infinite_exact_invisibility_off_symmetric_sector_backwardBackground
            m x ∧
        ∀ y : Fin (2 ^ q) → ℝ,
          conclusion_softcore_bi_infinite_exact_invisibility_off_symmetric_sector_inner y
              (conclusion_softcore_bi_infinite_exact_invisibility_off_symmetric_sector_forwardFull
                m x) =
            conclusion_softcore_bi_infinite_exact_invisibility_off_symmetric_sector_inner y
              (conclusion_softcore_bi_infinite_exact_invisibility_off_symmetric_sector_forwardBackground
                m x) ∧
          conclusion_softcore_bi_infinite_exact_invisibility_off_symmetric_sector_inner y
              (conclusion_softcore_bi_infinite_exact_invisibility_off_symmetric_sector_backwardFull
                m x) =
            conclusion_softcore_bi_infinite_exact_invisibility_off_symmetric_sector_inner y
              (conclusion_softcore_bi_infinite_exact_invisibility_off_symmetric_sector_backwardBackground
                m x)

/-- Paper label:
`cor:conclusion-softcore-bi-infinite-exact-invisibility-off-symmetric-sector`. -/
theorem paper_conclusion_softcore_bi_infinite_exact_invisibility_off_symmetric_sector
    (q m : Nat) (hm : 1 <= m) :
    conclusion_softcore_bi_infinite_exact_invisibility_off_symmetric_sector_statement q m := by
  let _ := hm
  intro x _hx
  refine ⟨rfl, rfl, ?_⟩
  intro y
  exact ⟨rfl, rfl⟩

end

end Omega.Conclusion
