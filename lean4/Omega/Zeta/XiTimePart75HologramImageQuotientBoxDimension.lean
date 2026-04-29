import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Zeta.XiTimePart75HologramPrefixCylinderCosetEquivalence

namespace Omega.Zeta

universe u v

noncomputable section

/-- Base scale `B = 2^L` for the two-coordinate hologram quotient. -/
def xi_time_part75_hologram_image_quotient_box_dimension_base (L : ℕ) : ℕ :=
  2 ^ L

/-- Concrete data for quotient occupancy.  The equivalence packages the preceding
prefix-cylinder/coset bijection at every depth, and `allCosets_card` records the ambient
two-coordinate quotient count. -/
structure xi_time_part75_hologram_image_quotient_box_dimension_Data where
  E : Type u
  Coset : ℕ → Type v
  fintypeE : Fintype E
  fintypeCoset : ∀ n, Fintype (Coset n)
  decidableEqCoset : ∀ n, DecidableEq (Coset n)
  occupiedCosets : ∀ n, Finset (Coset n)
  prefixToOccupiedCoset :
    ∀ n, (Fin n → E) ≃ {c : Coset n // c ∈ occupiedCosets n}
  L : ℕ
  L_pos : 0 < L
  allCosets_card :
    ∀ n, Fintype.card (Coset n) =
      xi_time_part75_hologram_image_quotient_box_dimension_base L ^ (2 * n)

/-- Occupied cosets at depth `n`. -/
def xi_time_part75_hologram_image_quotient_box_dimension_occupied_count
    (D : xi_time_part75_hologram_image_quotient_box_dimension_Data) (n : ℕ) : ℕ :=
  letI : Fintype (D.Coset n) := D.fintypeCoset n
  letI : DecidableEq (D.Coset n) := D.decidableEqCoset n
  (D.occupiedCosets n).card

/-- Total ambient quotient cosets at depth `n`. -/
def xi_time_part75_hologram_image_quotient_box_dimension_total_count
    (D : xi_time_part75_hologram_image_quotient_box_dimension_Data) (n : ℕ) : ℕ :=
  xi_time_part75_hologram_image_quotient_box_dimension_base D.L ^ (2 * n)

/-- The logarithmic growth quotient at depth `n`. -/
def xi_time_part75_hologram_image_quotient_box_dimension_growth_ratio
    (D : xi_time_part75_hologram_image_quotient_box_dimension_Data) (n : ℕ) : ℝ :=
  Real.log
      (xi_time_part75_hologram_image_quotient_box_dimension_occupied_count D n : ℝ) /
    Real.log ((xi_time_part75_hologram_image_quotient_box_dimension_base D.L : ℝ) ^ n)

/-- The common lower/upper box dimension determined by the prefix entropy. -/
def xi_time_part75_hologram_image_quotient_box_dimension_value
    (D : xi_time_part75_hologram_image_quotient_box_dimension_Data) : ℝ :=
  letI : Fintype D.E := D.fintypeE
  Real.log (Fintype.card D.E : ℝ) /
    Real.log (xi_time_part75_hologram_image_quotient_box_dimension_base D.L : ℝ)

/-- The theorem statement: occupied cosets, total cosets, and the resulting logarithmic
box-dimension quotient all have the advertised closed forms. -/
def xi_time_part75_hologram_image_quotient_box_dimension_statement
    (D : xi_time_part75_hologram_image_quotient_box_dimension_Data) : Prop :=
  (∀ n, 1 ≤ n →
    letI : Fintype D.E := D.fintypeE;
    letI : Fintype (D.Coset n) := D.fintypeCoset n;
    xi_time_part75_hologram_image_quotient_box_dimension_occupied_count D n =
        Fintype.card D.E ^ n ∧
      Fintype.card (D.Coset n) =
        xi_time_part75_hologram_image_quotient_box_dimension_total_count D n ∧
      xi_time_part75_hologram_image_quotient_box_dimension_growth_ratio D n =
        xi_time_part75_hologram_image_quotient_box_dimension_value D) ∧
    xi_time_part75_hologram_image_quotient_box_dimension_value D =
      (letI : Fintype D.E := D.fintypeE;
        Real.log (Fintype.card D.E : ℝ) / ((D.L : ℝ) * Real.log 2))

lemma xi_time_part75_hologram_image_quotient_box_dimension_occupied_card
    (D : xi_time_part75_hologram_image_quotient_box_dimension_Data) (n : ℕ) :
    letI : Fintype D.E := D.fintypeE
    xi_time_part75_hologram_image_quotient_box_dimension_occupied_count D n =
      Fintype.card D.E ^ n := by
  letI : Fintype D.E := D.fintypeE
  letI : Fintype (D.Coset n) := D.fintypeCoset n
  letI : DecidableEq (D.Coset n) := D.decidableEqCoset n
  have hcard :
      Fintype.card (Fin n → D.E) =
        Fintype.card {c : D.Coset n // c ∈ D.occupiedCosets n} :=
    Fintype.card_congr (D.prefixToOccupiedCoset n)
  calc
    xi_time_part75_hologram_image_quotient_box_dimension_occupied_count D n =
        Fintype.card {c : D.Coset n // c ∈ D.occupiedCosets n} := by
      simp [xi_time_part75_hologram_image_quotient_box_dimension_occupied_count,
        Fintype.card_coe]
    _ = Fintype.card (Fin n → D.E) := hcard.symm
    _ = Fintype.card D.E ^ n := by
      rw [Fintype.card_fun, Fintype.card_fin]

lemma xi_time_part75_hologram_image_quotient_box_dimension_growth_ratio_eq
    (D : xi_time_part75_hologram_image_quotient_box_dimension_Data) {n : ℕ} (hn : 1 ≤ n) :
    xi_time_part75_hologram_image_quotient_box_dimension_growth_ratio D n =
      xi_time_part75_hologram_image_quotient_box_dimension_value D := by
  letI : Fintype D.E := D.fintypeE
  have hoccupied :=
    xi_time_part75_hologram_image_quotient_box_dimension_occupied_card D n
  have hn_ne : (n : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hn)
  have hbase_gt_one :
      (1 : ℝ) < xi_time_part75_hologram_image_quotient_box_dimension_base D.L := by
    have hpow : 1 < 2 ^ D.L := Nat.one_lt_pow (ne_of_gt D.L_pos) (by norm_num : 1 < 2)
    exact_mod_cast hpow
  have hlog_base_ne :
      Real.log (xi_time_part75_hologram_image_quotient_box_dimension_base D.L : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos hbase_gt_one)
  calc
    xi_time_part75_hologram_image_quotient_box_dimension_growth_ratio D n =
        Real.log ((Fintype.card D.E ^ n : ℕ) : ℝ) /
          Real.log ((xi_time_part75_hologram_image_quotient_box_dimension_base D.L : ℝ) ^ n) := by
      rw [xi_time_part75_hologram_image_quotient_box_dimension_growth_ratio, hoccupied]
    _ =
        Real.log ((Fintype.card D.E : ℝ) ^ n) /
          Real.log ((xi_time_part75_hologram_image_quotient_box_dimension_base D.L : ℝ) ^ n) := by
      simp [Nat.cast_pow]
    _ =
        ((n : ℝ) * Real.log (Fintype.card D.E : ℝ)) /
          ((n : ℝ) *
            Real.log (xi_time_part75_hologram_image_quotient_box_dimension_base D.L : ℝ)) := by
      rw [Real.log_pow, Real.log_pow]
    _ = xi_time_part75_hologram_image_quotient_box_dimension_value D := by
      rw [xi_time_part75_hologram_image_quotient_box_dimension_value]
      field_simp [hn_ne, hlog_base_ne]

lemma xi_time_part75_hologram_image_quotient_box_dimension_value_binary
    (D : xi_time_part75_hologram_image_quotient_box_dimension_Data) :
    xi_time_part75_hologram_image_quotient_box_dimension_value D =
      (letI : Fintype D.E := D.fintypeE;
        Real.log (Fintype.card D.E : ℝ) / ((D.L : ℝ) * Real.log 2)) := by
  letI : Fintype D.E := D.fintypeE
  have hbase_log :
      Real.log (xi_time_part75_hologram_image_quotient_box_dimension_base D.L : ℝ) =
        (D.L : ℝ) * Real.log 2 := by
    simp [xi_time_part75_hologram_image_quotient_box_dimension_base, Nat.cast_pow,
      Real.log_pow]
  rw [xi_time_part75_hologram_image_quotient_box_dimension_value, hbase_log]

/-- Paper label: `cor:xi-time-part75-hologram-image-quotient-box-dimension`. -/
theorem paper_xi_time_part75_hologram_image_quotient_box_dimension
    (D : xi_time_part75_hologram_image_quotient_box_dimension_Data) :
    xi_time_part75_hologram_image_quotient_box_dimension_statement D := by
  constructor
  · intro n hn
    letI : Fintype D.E := D.fintypeE
    letI : Fintype (D.Coset n) := D.fintypeCoset n
    exact ⟨xi_time_part75_hologram_image_quotient_box_dimension_occupied_card D n,
      D.allCosets_card n,
      xi_time_part75_hologram_image_quotient_box_dimension_growth_ratio_eq D hn⟩
  · exact xi_time_part75_hologram_image_quotient_box_dimension_value_binary D

end

end Omega.Zeta
