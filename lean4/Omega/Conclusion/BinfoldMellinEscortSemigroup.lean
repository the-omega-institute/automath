import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- The two-atom base law whose Mellin tilts recover the escort family. -/
def binfoldMellinBaseLaw (φ : ℝ) : Bool → ℝ
  | false => φ / (1 + φ)
  | true => 1 / (1 + φ)

/-- The explicit escort law obtained after tilting the two-atom base law. -/
def binfoldMellinEscortLaw (φ q : ℝ) : Bool → ℝ
  | false => φ ^ (q + 1) / (1 + φ ^ (q + 1))
  | true => 1 / (1 + φ ^ (q + 1))

/-- The Mellin-side mgf of the escort law evaluated on the two-point support `{0, -log φ}`. -/
def binfoldMellinEscortMgf (φ q s : ℝ) : ℝ :=
  binfoldMellinEscortLaw φ q false +
    binfoldMellinEscortLaw φ q true * φ ^ (-s)

/-- One Mellin tilt step from the escort law at parameter `q` by exponent `s`. -/
def binfoldMellinTilt (φ q s : ℝ) : Bool → ℝ
  | false => binfoldMellinEscortLaw φ q false / binfoldMellinEscortMgf φ q s
  | true => binfoldMellinEscortLaw φ q true * φ ^ (-s) / binfoldMellinEscortMgf φ q s

/-- Concrete package for the binary Mellin escort family: the base law is the `q = 0` escort law,
the mgf has the closed two-atom form, one tilt renormalizes to the exponent sum, and successive
tilts therefore satisfy the additive semigroup law. -/
def BinfoldMellinEscortSemigroup (φ : ℝ) : Prop :=
  0 < φ ∧
    binfoldMellinBaseLaw φ = binfoldMellinEscortLaw φ 0 ∧
    (∀ q s : ℝ,
      binfoldMellinEscortMgf φ q s = (φ ^ (q + 1) + φ ^ (-s)) / (1 + φ ^ (q + 1))) ∧
    (∀ q s : ℝ, binfoldMellinTilt φ q s = binfoldMellinEscortLaw φ (q + s)) ∧
    (∀ q s t : ℝ, binfoldMellinTilt φ (q + s) t = binfoldMellinTilt φ q (s + t))

private lemma binfoldMellinBaseLaw_eq_escort_zero {φ : ℝ} :
    binfoldMellinBaseLaw φ = binfoldMellinEscortLaw φ 0 := by
  ext b
  cases b <;> simp [binfoldMellinBaseLaw, binfoldMellinEscortLaw, Real.rpow_one]

private lemma binfoldMellinEscortMgf_closed {φ : ℝ} (hφ : 0 < φ) (q s : ℝ) :
    binfoldMellinEscortMgf φ q s = (φ ^ (q + 1) + φ ^ (-s)) / (1 + φ ^ (q + 1)) := by
  have hden : (1 + φ ^ (q + 1) : ℝ) ≠ 0 := by positivity
  unfold binfoldMellinEscortMgf binfoldMellinEscortLaw
  field_simp [hden]

private lemma binfoldMellinTilt_false_closed {φ : ℝ} (hφ : 0 < φ) (q s : ℝ) :
    binfoldMellinTilt φ q s false = φ ^ (q + s + 1) / (1 + φ ^ (q + s + 1)) := by
  have hφs_ne : (φ ^ s : ℝ) ≠ 0 := by positivity
  have hq_ne : (1 + φ ^ (q + 1) : ℝ) ≠ 0 := by positivity
  have hmgf_ne : (binfoldMellinEscortMgf φ q s : ℝ) ≠ 0 := by
    rw [binfoldMellinEscortMgf_closed hφ]
    positivity
  have hmul : φ ^ (q + s + 1) = φ ^ (q + 1) * φ ^ s := by
    calc
      φ ^ (q + s + 1) = φ ^ ((q + 1) + s) := by congr 1; ring
      _ = φ ^ (q + 1) * φ ^ s := by rw [Real.rpow_add hφ]
  calc
    binfoldMellinTilt φ q s false
        = φ ^ (q + 1) / (φ ^ (q + 1) + φ ^ (-s)) := by
            unfold binfoldMellinTilt binfoldMellinEscortLaw
            rw [binfoldMellinEscortMgf_closed hφ]
            field_simp [hq_ne, hmgf_ne]
    _ = (φ ^ (q + 1) * φ ^ s) / ((φ ^ (q + 1) + φ ^ (-s)) * φ ^ s) := by
          field_simp [hφs_ne]
    _ = φ ^ (q + s + 1) / (1 + φ ^ (q + s + 1)) := by
          rw [Real.rpow_neg hφ.le]
          field_simp [hφs_ne]
          rw [hmul]
          ring

private lemma binfoldMellinTilt_true_closed {φ : ℝ} (hφ : 0 < φ) (q s : ℝ) :
    binfoldMellinTilt φ q s true = 1 / (1 + φ ^ (q + s + 1)) := by
  have hφs_ne : (φ ^ s : ℝ) ≠ 0 := by positivity
  have hq_ne : (1 + φ ^ (q + 1) : ℝ) ≠ 0 := by positivity
  have hmgf_ne : (binfoldMellinEscortMgf φ q s : ℝ) ≠ 0 := by
    rw [binfoldMellinEscortMgf_closed hφ]
    positivity
  have hmul : φ ^ (q + s + 1) = φ ^ (q + 1) * φ ^ s := by
    calc
      φ ^ (q + s + 1) = φ ^ ((q + 1) + s) := by congr 1; ring
      _ = φ ^ (q + 1) * φ ^ s := by rw [Real.rpow_add hφ]
  calc
    binfoldMellinTilt φ q s true
        = φ ^ (-s) / (φ ^ (q + 1) + φ ^ (-s)) := by
            unfold binfoldMellinTilt binfoldMellinEscortLaw
            rw [binfoldMellinEscortMgf_closed hφ]
            field_simp [hq_ne, hmgf_ne]
    _ = (φ ^ (-s) * φ ^ s) / ((φ ^ (q + 1) + φ ^ (-s)) * φ ^ s) := by
          field_simp [hφs_ne]
    _ = 1 / (1 + φ ^ (q + s + 1)) := by
          rw [Real.rpow_neg hφ.le]
          field_simp [hφs_ne]
          rw [hmul]
          ring

private lemma binfoldMellinTilt_closed {φ : ℝ} (hφ : 0 < φ) (q s : ℝ) :
    binfoldMellinTilt φ q s = binfoldMellinEscortLaw φ (q + s) := by
  ext b
  cases b
  · simp [binfoldMellinEscortLaw, binfoldMellinTilt_false_closed hφ]
  · simp [binfoldMellinEscortLaw, binfoldMellinTilt_true_closed hφ]

/-- Paper label: `thm:conclusion-binfold-mellin-escort-semigroup`. For the golden two-atom base
law, the escort normalization and the Mellin mgf are explicit, and tilting twice adds the Mellin
exponents. -/
theorem paper_conclusion_binfold_mellin_escort_semigroup :
    BinfoldMellinEscortSemigroup Real.goldenRatio := by
  refine ⟨Real.goldenRatio_pos, ?_, ?_, ?_, ?_⟩
  · exact binfoldMellinBaseLaw_eq_escort_zero
  · intro q s
    exact binfoldMellinEscortMgf_closed Real.goldenRatio_pos q s
  · intro q s
    exact binfoldMellinTilt_closed Real.goldenRatio_pos q s
  · intro q s t
    rw [binfoldMellinTilt_closed Real.goldenRatio_pos, binfoldMellinTilt_closed Real.goldenRatio_pos]
    congr 1
    ring

end

end Omega.Conclusion
