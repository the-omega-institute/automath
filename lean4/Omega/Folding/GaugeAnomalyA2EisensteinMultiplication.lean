import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic
import Omega.CircleDimension.S4V4PrymA2PolarizedIsogenyRigidity

namespace Omega.Folding

open Matrix

/-- The standard order-three deck transformation on the rank-two Prym lattice. -/
def gaugeAnomalyOrderThreeGenerator : Matrix (Fin 2) (Fin 2) ℤ :=
  Omega.CircleDimension.s4v4StandardGenerator

/-- Concrete Prym data for the `A₂` gauge-anomaly model. The only geometric datum needed here is
the induced order-three deck transformation on the Prym lattice. -/
structure GaugeAnomalyPrymData where
  deckTransformation : Matrix (Fin 2) (Fin 2) ℤ
  hdeck : deckTransformation = gaugeAnomalyOrderThreeGenerator

/-- Integral coordinates for `ℤ[ζ₃] = ℤ ⊕ ℤ·σ` in the modeled endomorphism algebra. -/
abbrev EisensteinInteger := ℤ × ℤ

/-- Rational coordinates for `ℚ(ζ₃) = ℚ ⊕ ℚ·σ`. -/
abbrev EisensteinRational := ℚ × ℚ

/-- The induced integral Eisenstein action on the Prym lattice. -/
def eisensteinIntegerEmbedding (_ : GaugeAnomalyPrymData) (z : EisensteinInteger) :
    Matrix (Fin 2) (Fin 2) ℤ :=
  !![z.1, -z.2; z.2, z.1 - z.2]

/-- The induced rational Eisenstein action on the Prym lattice. -/
def eisensteinRationalEmbedding (_ : GaugeAnomalyPrymData) (z : EisensteinRational) :
    Matrix (Fin 2) (Fin 2) ℚ :=
  !![z.1, -z.2; z.2, z.1 - z.2]

/-- The relation `1 + σ + σ² = 0` on the Prym kernel together with the induced integral and
rational Eisenstein embeddings. -/
def HasEisensteinMultiplication (P : GaugeAnomalyPrymData) : Prop :=
  P.deckTransformation ^ 3 = 1 ∧
    ((1 : Matrix (Fin 2) (Fin 2) ℤ) + P.deckTransformation + P.deckTransformation ^ 2 = 0) ∧
    Function.Injective (eisensteinIntegerEmbedding P) ∧
    Function.Injective (eisensteinRationalEmbedding P)

lemma gaugeAnomalyOrderThreeGenerator_cube : gaugeAnomalyOrderThreeGenerator ^ 3 = 1 := by
  simpa [gaugeAnomalyOrderThreeGenerator] using
    Omega.CircleDimension.standardGenerator_cube

lemma gaugeAnomalyOrderThreeGenerator_relation :
    (1 : Matrix (Fin 2) (Fin 2) ℤ) + gaugeAnomalyOrderThreeGenerator +
      gaugeAnomalyOrderThreeGenerator ^ 2 = 0 := by
  have hsquare : gaugeAnomalyOrderThreeGenerator ^ 2 = !![-1, 1; -1, 0] := by
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [gaugeAnomalyOrderThreeGenerator, Omega.CircleDimension.s4v4StandardGenerator, pow_two,
        Matrix.mul_apply, Fin.sum_univ_two]
  rw [hsquare]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [gaugeAnomalyOrderThreeGenerator, Omega.CircleDimension.s4v4StandardGenerator]

lemma eisensteinIntegerEmbedding_formula (P : GaugeAnomalyPrymData) (m n : ℤ) :
    eisensteinIntegerEmbedding P (m, n) = !![m, -n; n, m - n] := by
  rfl

lemma eisensteinRationalEmbedding_formula (P : GaugeAnomalyPrymData) (u v : ℚ) :
    eisensteinRationalEmbedding P (u, v) = !![u, -v; v, u - v] := by
  rfl

lemma eisensteinIntegerEmbedding_injective (P : GaugeAnomalyPrymData) :
    Function.Injective (eisensteinIntegerEmbedding P) := by
  intro x y hxy
  rcases x with ⟨m, n⟩
  rcases y with ⟨p, q⟩
  have h01 := congrArg (fun M => M 0 1) hxy
  rw [eisensteinIntegerEmbedding_formula P m n, eisensteinIntegerEmbedding_formula P p q] at h01
  have h00 := congrArg (fun M => M 0 0) hxy
  rw [eisensteinIntegerEmbedding_formula P m n, eisensteinIntegerEmbedding_formula P p q] at h00
  simp at h01 h00
  have hnq : n = q := by
    linarith [h01]
  exact Prod.ext h00 hnq

lemma eisensteinRationalEmbedding_injective (P : GaugeAnomalyPrymData) :
    Function.Injective (eisensteinRationalEmbedding P) := by
  intro x y hxy
  rcases x with ⟨u, v⟩
  rcases y with ⟨r, s⟩
  have h01 := congrArg (fun M => M 0 1) hxy
  rw [eisensteinRationalEmbedding_formula P u v, eisensteinRationalEmbedding_formula P r s] at h01
  have h00 := congrArg (fun M => M 0 0) hxy
  rw [eisensteinRationalEmbedding_formula P u v, eisensteinRationalEmbedding_formula P r s] at h00
  simp at h01 h00
  have hvs : v = s := by
    linarith [h01]
  exact Prod.ext h00 hvs

/-- The order-three deck transformation on the modeled Prym lattice satisfies the Eisenstein
relation `1 + σ + σ² = 0`, so the integral and rational Eisenstein rings embed in the Prym
endomorphism algebra.
    thm:fold-gauge-anomaly-a2-eisenstein-multiplication -/
theorem paper_fold_gauge_anomaly_a2_eisenstein_multiplication (P : GaugeAnomalyPrymData) :
    HasEisensteinMultiplication P := by
  refine ⟨?_, ?_, eisensteinIntegerEmbedding_injective P, eisensteinRationalEmbedding_injective P⟩
  · simpa [P.hdeck] using gaugeAnomalyOrderThreeGenerator_cube
  · simpa [P.hdeck] using gaugeAnomalyOrderThreeGenerator_relation

end Omega.Folding
