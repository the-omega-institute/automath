import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.OperatorAlgebra

/-- The four central `χ`-sectors coming from the two commuting `±1` symmetries. -/
inductive ChiSector
  | pp
  | pm
  | mp
  | mm
  deriving DecidableEq, Fintype

/-- The central idempotent cutting out a single `χ`-sector in the commutative four-sector model. -/
def chiSectorIdempotent (σ : ChiSector) : ChiSector → ℝ :=
  fun τ => if σ = τ then 1 else 0

/-- The sectorwise model for `I - K`. -/
def chiSectorShift (K : ChiSector → ℝ) : ChiSector → ℝ :=
  fun σ => 1 - K σ

/-- The `σ`-sector summand in the direct-sum expansion of `I - K`. -/
def chiSectorShiftComponent (K : ChiSector → ℝ) (σ : ChiSector) : ChiSector → ℝ :=
  fun τ => chiSectorIdempotent σ τ * chiSectorShift K τ

/-- The sectorwise Fuglede-Kadison factor recorded with a concrete trace weight `w σ`. -/
noncomputable def chiSectorFkdetFactor (w K : ChiSector → ℝ) (σ : ChiSector) : ℝ :=
  Real.exp (w σ * Real.log |chiSectorShift K σ|)

/-- The full four-sector Fuglede-Kadison determinant in the commutative model. -/
noncomputable def chiSectorFkdet (w K : ChiSector → ℝ) : ℝ :=
  Real.exp (∑ σ : ChiSector, w σ * Real.log |chiSectorShift K σ|)

/-- The inverse determinant package appearing in the `Z`-factorization. -/
noncomputable def chiSectorZeta (w K : ChiSector → ℝ) : ℝ :=
  (chiSectorFkdet w K)⁻¹

/-- Sectorwise inverse determinant factor. -/
noncomputable def chiSectorZetaFactor (w K : ChiSector → ℝ) (σ : ChiSector) : ℝ :=
  (chiSectorFkdetFactor w K σ)⁻¹

/-- Global resonance: one of the sector factors `1 - K σ` vanishes. -/
def chiSectorGlobalSpectrumCrossing (K : ChiSector → ℝ) : Prop :=
  ∏ σ : ChiSector, chiSectorShift K σ = 0

private lemma chiSectorIdempotent_mul_self (σ : ChiSector) :
    chiSectorIdempotent σ * chiSectorIdempotent σ = chiSectorIdempotent σ := by
  ext τ
  by_cases h : σ = τ
  · simp [chiSectorIdempotent, h]
  · simp [chiSectorIdempotent, h]

private lemma chiSectorIdempotent_sum :
    (∑ σ : ChiSector, chiSectorIdempotent σ) = fun _ => (1 : ℝ) := by
  ext τ
  simp [chiSectorIdempotent]

private lemma chiSectorShift_direct_sum (K : ChiSector → ℝ) :
    chiSectorShift K = ∑ σ : ChiSector, chiSectorShiftComponent K σ := by
  ext τ
  simp [chiSectorShiftComponent, chiSectorIdempotent, chiSectorShift]

/-- Concrete `χ`-sector factorization for the four-sector commutative model: the central
idempotents sum to `1`, `I - K` splits into the four sector summands, the logarithmic determinant
exponentiates to a product of sector factors, the corresponding inverse determinant also splits,
and the spectral crossing criterion reduces to the union of the four sector conditions.
    thm:op-algebra-fkdet-chi-sector-factorization -/
theorem paper_op_algebra_fkdet_chi_sector_factorization (w K : ChiSector → ℝ) :
    (∀ σ : ChiSector, chiSectorIdempotent σ * chiSectorIdempotent σ = chiSectorIdempotent σ) ∧
      (∑ σ : ChiSector, chiSectorIdempotent σ = fun _ => (1 : ℝ)) ∧
      chiSectorShift K = ∑ σ : ChiSector, chiSectorShiftComponent K σ ∧
      chiSectorFkdet w K = ∏ σ : ChiSector, chiSectorFkdetFactor w K σ ∧
      chiSectorZeta w K = ∏ σ : ChiSector, chiSectorZetaFactor w K σ ∧
      (chiSectorGlobalSpectrumCrossing K ↔ ∃ σ : ChiSector, K σ = 1) := by
  refine ⟨chiSectorIdempotent_mul_self, chiSectorIdempotent_sum, chiSectorShift_direct_sum K, ?_,
    ?_, ?_⟩
  · simpa [chiSectorFkdet, chiSectorFkdetFactor] using
      (Real.exp_sum (s := Finset.univ) (f := fun σ : ChiSector => w σ * Real.log |chiSectorShift K σ|))
  · rw [chiSectorZeta]
    rw [show chiSectorFkdet w K = ∏ σ : ChiSector, chiSectorFkdetFactor w K σ by
      simpa [chiSectorFkdet, chiSectorFkdetFactor] using
        (Real.exp_sum (s := Finset.univ)
          (f := fun σ : ChiSector => w σ * Real.log |chiSectorShift K σ|))]
    simp [chiSectorZetaFactor, Finset.prod_inv_distrib]
  · constructor
    · intro hcross
      rw [chiSectorGlobalSpectrumCrossing, Finset.prod_eq_zero_iff] at hcross
      rcases hcross with ⟨σ, -, hσ⟩
      have hK : K σ = 1 := by
        dsimp [chiSectorShift] at hσ
        linarith
      exact ⟨σ, hK⟩
    · rintro ⟨σ, hσ⟩
      rw [chiSectorGlobalSpectrumCrossing, Finset.prod_eq_zero_iff]
      refine ⟨σ, Finset.mem_univ σ, ?_⟩
      simp [chiSectorShift, hσ]

end Omega.OperatorAlgebra
