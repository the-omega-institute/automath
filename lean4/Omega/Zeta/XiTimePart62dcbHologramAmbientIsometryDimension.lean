import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Base scale for the ambient hologram package. -/
def xi_time_part62dcb_hologram_ambient_isometry_dimension_base (L : ℕ) : ℕ :=
  2 ^ L

/-- Agreement of two symbolic addresses on the first `n` digits. -/
def xi_time_part62dcb_hologram_ambient_isometry_dimension_prefixAgree
    (M n : ℕ) (a b : ℕ → Fin (M + 1)) : Prop :=
  ∀ i : Fin n, a i = b i

/-- Ambient agreement after coding each digit into the `B`-adic ambient line. -/
def xi_time_part62dcb_hologram_ambient_isometry_dimension_ambientAgree
    (M B n : ℕ) (code : Fin (M + 1) → Fin B) (a b : ℕ → Fin (M + 1)) : Prop :=
  ∀ i : Fin n, code (a i) = code (b i)

/-- Number of occupied depth-`n` prefix cylinders. -/
def xi_time_part62dcb_hologram_ambient_isometry_dimension_prefixCount
    (M n : ℕ) : ℕ :=
  Fintype.card (Fin n → Fin (M + 1))

/-- Logarithmic dimension quotient at depth `n`. -/
def xi_time_part62dcb_hologram_ambient_isometry_dimension_growthRatio
    (M L n : ℕ) : ℝ :=
  Real.log
      (xi_time_part62dcb_hologram_ambient_isometry_dimension_prefixCount M n : ℝ) /
    Real.log ((xi_time_part62dcb_hologram_ambient_isometry_dimension_base L : ℝ) ^ n)

/-- Closed-form symbolic dimension of the prefix hologram. -/
def xi_time_part62dcb_hologram_ambient_isometry_dimension_dimensionValue
    (M L : ℕ) : ℝ :=
  Real.log (M + 1 : ℝ) /
    Real.log (xi_time_part62dcb_hologram_ambient_isometry_dimension_base L : ℝ)

/-- Ambient two-dimensional Haar decay ratio for one additional prefix digit. -/
def xi_time_part62dcb_hologram_ambient_isometry_dimension_haarDecayRatio
    (M L : ℕ) : ℝ :=
  (M + 1 : ℝ) /
    (xi_time_part62dcb_hologram_ambient_isometry_dimension_base L : ℝ) ^ (2 : ℕ)

lemma xi_time_part62dcb_hologram_ambient_isometry_dimension_prefix_ambient_iff
    {M B n : ℕ} {code : Fin (M + 1) → Fin B} (hcode : Function.Injective code)
    (a b : ℕ → Fin (M + 1)) :
    xi_time_part62dcb_hologram_ambient_isometry_dimension_prefixAgree M n a b ↔
      xi_time_part62dcb_hologram_ambient_isometry_dimension_ambientAgree M B n code a b := by
  constructor
  · intro h i
    exact congrArg code (h i)
  · intro h i
    exact hcode (h i)

lemma xi_time_part62dcb_hologram_ambient_isometry_dimension_prefixCount_eq
    (M n : ℕ) :
    xi_time_part62dcb_hologram_ambient_isometry_dimension_prefixCount M n =
      (M + 1) ^ n := by
  simp [xi_time_part62dcb_hologram_ambient_isometry_dimension_prefixCount]

lemma xi_time_part62dcb_hologram_ambient_isometry_dimension_selfSimilarCount
    (M n : ℕ) :
    xi_time_part62dcb_hologram_ambient_isometry_dimension_prefixCount M (n + 1) =
      (M + 1) *
        xi_time_part62dcb_hologram_ambient_isometry_dimension_prefixCount M n := by
  simp [xi_time_part62dcb_hologram_ambient_isometry_dimension_prefixCount, pow_succ,
    Nat.mul_comm]

lemma xi_time_part62dcb_hologram_ambient_isometry_dimension_growthRatio_eq
    {M L n : ℕ} (hL : 0 < L) (hn : 1 ≤ n) :
    xi_time_part62dcb_hologram_ambient_isometry_dimension_growthRatio M L n =
      xi_time_part62dcb_hologram_ambient_isometry_dimension_dimensionValue M L := by
  have hn_ne : (n : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hn)
  have hbase_gt_one :
      (1 : ℝ) < xi_time_part62dcb_hologram_ambient_isometry_dimension_base L := by
    have hpow : 1 < 2 ^ L := Nat.one_lt_pow (ne_of_gt hL) (by norm_num : 1 < 2)
    exact_mod_cast hpow
  have hlog_base_ne :
      Real.log (xi_time_part62dcb_hologram_ambient_isometry_dimension_base L : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos hbase_gt_one)
  calc
    xi_time_part62dcb_hologram_ambient_isometry_dimension_growthRatio M L n =
        Real.log ((M + 1 : ℝ) ^ n) /
          Real.log ((xi_time_part62dcb_hologram_ambient_isometry_dimension_base L : ℝ) ^ n) := by
      rw [xi_time_part62dcb_hologram_ambient_isometry_dimension_growthRatio,
        xi_time_part62dcb_hologram_ambient_isometry_dimension_prefixCount_eq]
      simp [Nat.cast_pow]
    _ =
        ((n : ℝ) * Real.log (M + 1 : ℝ)) /
          ((n : ℝ) *
            Real.log (xi_time_part62dcb_hologram_ambient_isometry_dimension_base L : ℝ)) := by
      rw [Real.log_pow, Real.log_pow]
    _ = xi_time_part62dcb_hologram_ambient_isometry_dimension_dimensionValue M L := by
      rw [xi_time_part62dcb_hologram_ambient_isometry_dimension_dimensionValue]
      field_simp [hn_ne, hlog_base_ne]

lemma xi_time_part62dcb_hologram_ambient_isometry_dimension_haarDecayRatio_lt_one
    {M L : ℕ} (hL : 0 < L)
    (hMB : M + 1 ≤ xi_time_part62dcb_hologram_ambient_isometry_dimension_base L) :
    xi_time_part62dcb_hologram_ambient_isometry_dimension_haarDecayRatio M L < 1 := by
  let B : ℝ := xi_time_part62dcb_hologram_ambient_isometry_dimension_base L
  have hbase_gt_one : (1 : ℝ) < B := by
    have hpow : 1 < 2 ^ L := Nat.one_lt_pow (ne_of_gt hL) (by norm_num : 1 < 2)
    simpa [B, xi_time_part62dcb_hologram_ambient_isometry_dimension_base] using
      (show (1 : ℝ) < (2 ^ L : ℕ) by exact_mod_cast hpow)
  have hbase_pos : (0 : ℝ) < B := lt_trans zero_lt_one hbase_gt_one
  have hMle : (M + 1 : ℝ) ≤ B := by
    simpa [B] using (show (M + 1 : ℝ) ≤
      (xi_time_part62dcb_hologram_ambient_isometry_dimension_base L : ℕ) by exact_mod_cast hMB)
  have hratio_le : (M + 1 : ℝ) / B ^ (2 : ℕ) ≤ B / B ^ (2 : ℕ) := by
    exact div_le_div_of_nonneg_right hMle (sq_nonneg B)
  have hB_div : B / B ^ (2 : ℕ) = 1 / B := by
    field_simp [ne_of_gt hbase_pos]
  have hone_div_lt : (1 : ℝ) / B < 1 := by
    rw [div_lt_iff₀ hbase_pos]
    nlinarith
  calc
    xi_time_part62dcb_hologram_ambient_isometry_dimension_haarDecayRatio M L =
        (M + 1 : ℝ) / B ^ (2 : ℕ) := by
      simp [xi_time_part62dcb_hologram_ambient_isometry_dimension_haarDecayRatio, B]
    _ ≤ B / B ^ (2 : ℕ) := hratio_le
    _ = 1 / B := hB_div
    _ < 1 := hone_div_lt

/-- Concrete package for
`thm:xi-time-part62dcb-hologram-ambient-isometry-dimension`.  It records the
self-similar prefix count, the ambient prefix-isometry rewrite, the logarithmic dimension
formula, and the strict ambient Haar decay ratio. -/
def xi_time_part62dcb_hologram_ambient_isometry_dimension_package : Prop :=
  ∀ (M L n B : ℕ) (code : Fin (M + 1) → Fin B),
    0 < L →
      B = xi_time_part62dcb_hologram_ambient_isometry_dimension_base L →
        M + 1 ≤ B →
          1 ≤ n →
            Function.Injective code →
              (∀ a b : ℕ → Fin (M + 1),
                xi_time_part62dcb_hologram_ambient_isometry_dimension_prefixAgree M n a b ↔
                  xi_time_part62dcb_hologram_ambient_isometry_dimension_ambientAgree
                    M B n code a b) ∧
                xi_time_part62dcb_hologram_ambient_isometry_dimension_prefixCount M (n + 1) =
                  (M + 1) *
                    xi_time_part62dcb_hologram_ambient_isometry_dimension_prefixCount M n ∧
                xi_time_part62dcb_hologram_ambient_isometry_dimension_prefixCount M n =
                  (M + 1) ^ n ∧
                xi_time_part62dcb_hologram_ambient_isometry_dimension_growthRatio M L n =
                  xi_time_part62dcb_hologram_ambient_isometry_dimension_dimensionValue M L ∧
                xi_time_part62dcb_hologram_ambient_isometry_dimension_haarDecayRatio M L < 1

/-- Paper label:
`thm:xi-time-part62dcb-hologram-ambient-isometry-dimension`. -/
theorem paper_xi_time_part62dcb_hologram_ambient_isometry_dimension :
    xi_time_part62dcb_hologram_ambient_isometry_dimension_package := by
  intro M L n B code hL hB hMB hn hcode
  subst B
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a b
    exact xi_time_part62dcb_hologram_ambient_isometry_dimension_prefix_ambient_iff hcode a b
  · exact xi_time_part62dcb_hologram_ambient_isometry_dimension_selfSimilarCount M n
  · exact xi_time_part62dcb_hologram_ambient_isometry_dimension_prefixCount_eq M n
  · exact xi_time_part62dcb_hologram_ambient_isometry_dimension_growthRatio_eq hL hn
  · exact xi_time_part62dcb_hologram_ambient_isometry_dimension_haarDecayRatio_lt_one hL hMB

end

end Omega.Zeta
