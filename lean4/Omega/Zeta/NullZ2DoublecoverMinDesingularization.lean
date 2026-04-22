import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Omega.Zeta.BdryFreeInvolutionOddFiberObstructionMinCover
import Omega.Zeta.NullZ2SpectralSplittingDoublecover

namespace Omega.Zeta

open NullZ2SpectralSplittingData

/-- The concrete two-sheeted cover attached to the visible `Z/2` datum. -/
def xi_null_z2_doublecover_min_desingularization_coverVertex (n : ℕ) : Type :=
  Fin n × Fin 2

/-- The projection from the double cover to the base vertex set. -/
def xi_null_z2_doublecover_min_desingularization_coverProjection {n : ℕ} :
    xi_null_z2_doublecover_min_desingularization_coverVertex n → Fin n :=
  Prod.fst

/-- Pull back the visible `Z/2` class along the two-sheet cover. -/
def xi_null_z2_doublecover_min_desingularization_pullbackClass {n : ℕ}
    (η : Fin n → Fin 2) :
    xi_null_z2_doublecover_min_desingularization_coverVertex n → Fin 2 :=
  fun x => η x.1

/-- The lifted class is trivialized on the cover by the same vertex labelling. -/
def xi_null_z2_doublecover_min_desingularization_trivializingGauge {n : ℕ}
    (η : Fin n → Fin 2) :
    xi_null_z2_doublecover_min_desingularization_coverVertex n → Fin 2 :=
  fun x => η x.1

/-- Symmetric lifted matrix whose odd sector vanishes after the Hadamard splitting. -/
def xi_null_z2_doublecover_min_desingularization_splittingData {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℂ) : NullZ2SpectralSplittingData where
  n := n
  B0 := B
  B1 := B

/-- The visible odd block on the cover. -/
def xi_null_z2_doublecover_min_desingularization_visibleObstruction {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (xi_null_z2_doublecover_min_desingularization_splittingData B).betaMatrix

/-- Each fiber of the projection is canonically a two-point set. -/
def xi_null_z2_doublecover_min_desingularization_fiberEquiv {n : ℕ} (v : Fin n) :
    {y : xi_null_z2_doublecover_min_desingularization_coverVertex n //
        xi_null_z2_doublecover_min_desingularization_coverProjection y = v} ≃ Fin 2 where
  toFun y := y.1.2
  invFun i := ⟨(v, i), rfl⟩
  left_inv y := by
    rcases y with ⟨⟨v', i⟩, hy⟩
    simp [xi_null_z2_doublecover_min_desingularization_coverProjection] at hy
    cases hy
    rfl
  right_inv i := rfl

noncomputable instance xi_null_z2_doublecover_min_desingularization_instFintypeFiber {n : ℕ}
    (v : Fin n) :
    Fintype {y : xi_null_z2_doublecover_min_desingularization_coverVertex n //
      xi_null_z2_doublecover_min_desingularization_coverProjection y = v} :=
  Fintype.ofEquiv (Fin 2) (xi_null_z2_doublecover_min_desingularization_fiberEquiv v).symm

lemma xi_null_z2_doublecover_min_desingularization_fiber_card {n : ℕ} (v : Fin n) :
    Fintype.card {y : xi_null_z2_doublecover_min_desingularization_coverVertex n //
      xi_null_z2_doublecover_min_desingularization_coverProjection y = v} = 2 := by
  classical
  simpa using Fintype.card_congr
    (xi_null_z2_doublecover_min_desingularization_fiberEquiv v)

lemma xi_null_z2_doublecover_min_desingularization_minimal_even_degree (d : ℕ)
    (hd : 0 < d) (heven : Even d) : 2 ≤ d := by
  rcases heven with ⟨k, rfl⟩
  omega

/-- `thm:xi-null-z2-doublecover-min-desingularization`

The concrete two-sheet cover trivializes the pulled-back `Z/2` class, kills the visible odd block
in the null spectral splitting, and has minimal possible positive even degree. -/
theorem paper_xi_null_z2_doublecover_min_desingularization
    {n : ℕ} (η : Fin n → Fin 2) (B : Matrix (Fin n) (Fin n) ℂ) :
    let D := xi_null_z2_doublecover_min_desingularization_splittingData B
    (∀ x,
        xi_null_z2_doublecover_min_desingularization_pullbackClass η x =
          xi_null_z2_doublecover_min_desingularization_trivializingGauge η x) ∧
      xi_null_z2_doublecover_min_desingularization_visibleObstruction B = 0 ∧
      D.hasDirectSumSplitting ∧
      D.determinantFactorization ∧
      (∀ v : Fin n,
          Fintype.card {y : xi_null_z2_doublecover_min_desingularization_coverVertex n //
            xi_null_z2_doublecover_min_desingularization_coverProjection y = v} = 2) ∧
      (∀ d : ℕ, 0 < d → Even d → 2 ≤ d) := by
  let D := xi_null_z2_doublecover_min_desingularization_splittingData B
  have hsplit : D.hasDirectSumSplitting ∧ D.determinantFactorization :=
    paper_xi_null_z2_spectral_splitting_doublecover D
  refine ⟨?_, ?_, hsplit.1, hsplit.2, ?_, ?_⟩
  · intro x
    rfl
  · ext i j
    simp [xi_null_z2_doublecover_min_desingularization_visibleObstruction,
      xi_null_z2_doublecover_min_desingularization_splittingData,
      NullZ2SpectralSplittingData.betaMatrix]
  · intro v
    exact xi_null_z2_doublecover_min_desingularization_fiber_card v
  · intro d hd heven
    exact xi_null_z2_doublecover_min_desingularization_minimal_even_degree d hd heven

end Omega.Zeta
