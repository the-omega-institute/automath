import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Concrete data for the congruence-block Abel--Weil package: a common base `β`, a positive
modulus `m`, and the residue-class coefficients of the block expansion. -/
structure XiCongruenceBlockAbelWeilResidueLockingData where
  xi_congruence_block_abel_weil_residue_locking_base : ℂ
  xi_congruence_block_abel_weil_residue_locking_base_ne_zero :
    xi_congruence_block_abel_weil_residue_locking_base ≠ 0
  xi_congruence_block_abel_weil_residue_locking_modulus : ℕ
  xi_congruence_block_abel_weil_residue_locking_modulus_pos :
    0 < xi_congruence_block_abel_weil_residue_locking_modulus
  xi_congruence_block_abel_weil_residue_locking_coeff :
    Fin xi_congruence_block_abel_weil_residue_locking_modulus → ℂ

namespace XiCongruenceBlockAbelWeilResidueLockingData

/-- The finite congruence-block expansion before factoring out the common geometric kernel. -/
def xi_congruence_block_abel_weil_residue_locking_main_series
    (D : XiCongruenceBlockAbelWeilResidueLockingData) (N : ℕ) : ℂ :=
  Finset.univ.sum fun r : Fin D.xi_congruence_block_abel_weil_residue_locking_modulus =>
    (Finset.range N).sum fun n =>
      D.xi_congruence_block_abel_weil_residue_locking_coeff r *
        D.xi_congruence_block_abel_weil_residue_locking_base ^
          ((r : ℕ) + n * D.xi_congruence_block_abel_weil_residue_locking_modulus)

/-- The same finite expansion regrouped by residue classes modulo `m`. -/
def xi_congruence_block_abel_weil_residue_locking_grouped_series
    (D : XiCongruenceBlockAbelWeilResidueLockingData) (N : ℕ) : ℂ :=
  Finset.univ.sum fun r : Fin D.xi_congruence_block_abel_weil_residue_locking_modulus =>
    D.xi_congruence_block_abel_weil_residue_locking_coeff r *
        D.xi_congruence_block_abel_weil_residue_locking_base ^ (r : ℕ) *
          (Finset.range N).sum fun n =>
            (D.xi_congruence_block_abel_weil_residue_locking_base ^
              D.xi_congruence_block_abel_weil_residue_locking_modulus) ^ n

/-- The Abel--Weil coefficient attached to residue class `r`. -/
def xi_congruence_block_abel_weil_residue_locking_abel_weil_coefficient
    (D : XiCongruenceBlockAbelWeilResidueLockingData)
    (r : Fin D.xi_congruence_block_abel_weil_residue_locking_modulus) : ℂ :=
  D.xi_congruence_block_abel_weil_residue_locking_coeff r *
    D.xi_congruence_block_abel_weil_residue_locking_base ^ (r : ℕ)

/-- The common pole induced by the shared denominator `1 - u β^m`. -/
def xi_congruence_block_abel_weil_residue_locking_common_pole
    (D : XiCongruenceBlockAbelWeilResidueLockingData) : ℂ :=
  (D.xi_congruence_block_abel_weil_residue_locking_base ^
    D.xi_congruence_block_abel_weil_residue_locking_modulus)⁻¹

/-- The explicit Abel--Weil residue coefficient at the common pole. -/
def xi_congruence_block_abel_weil_residue_locking_residue_formula
    (D : XiCongruenceBlockAbelWeilResidueLockingData)
    (r : Fin D.xi_congruence_block_abel_weil_residue_locking_modulus) : ℂ :=
  D.xi_congruence_block_abel_weil_residue_locking_abel_weil_coefficient r *
    D.xi_congruence_block_abel_weil_residue_locking_common_pole

/-- The equivalent derivative-of-the-denominator residue witness. -/
def xi_congruence_block_abel_weil_residue_locking_residue_witness
    (D : XiCongruenceBlockAbelWeilResidueLockingData)
    (r : Fin D.xi_congruence_block_abel_weil_residue_locking_modulus) : ℂ :=
  -D.xi_congruence_block_abel_weil_residue_locking_abel_weil_coefficient r /
    (-(D.xi_congruence_block_abel_weil_residue_locking_base ^
      D.xi_congruence_block_abel_weil_residue_locking_modulus))

/-- Paper-facing congruence-block package: the finite series regroups by residue classes, the
common geometric kernel satisfies the standard closed form identity, the common pole is explicit,
and each residue class has the Abel--Weil coefficient dictated by that pole. -/
def statement (D : XiCongruenceBlockAbelWeilResidueLockingData) : Prop :=
  (∀ N, D.xi_congruence_block_abel_weil_residue_locking_main_series N =
      D.xi_congruence_block_abel_weil_residue_locking_grouped_series N) ∧
    (∀ N,
      ((Finset.range N).sum fun n =>
          (D.xi_congruence_block_abel_weil_residue_locking_base ^
            D.xi_congruence_block_abel_weil_residue_locking_modulus) ^ n) *
          (D.xi_congruence_block_abel_weil_residue_locking_base ^
            D.xi_congruence_block_abel_weil_residue_locking_modulus - 1) =
        (D.xi_congruence_block_abel_weil_residue_locking_base ^
          D.xi_congruence_block_abel_weil_residue_locking_modulus) ^ N - 1) ∧
    (1 - D.xi_congruence_block_abel_weil_residue_locking_common_pole *
        D.xi_congruence_block_abel_weil_residue_locking_base ^
          D.xi_congruence_block_abel_weil_residue_locking_modulus = 0) ∧
    ∀ r : Fin D.xi_congruence_block_abel_weil_residue_locking_modulus,
      D.xi_congruence_block_abel_weil_residue_locking_residue_witness r =
        D.xi_congruence_block_abel_weil_residue_locking_residue_formula r

lemma xi_congruence_block_abel_weil_residue_locking_grouping
    (D : XiCongruenceBlockAbelWeilResidueLockingData) (N : ℕ) :
    D.xi_congruence_block_abel_weil_residue_locking_main_series N =
      D.xi_congruence_block_abel_weil_residue_locking_grouped_series N := by
  unfold xi_congruence_block_abel_weil_residue_locking_main_series
    xi_congruence_block_abel_weil_residue_locking_grouped_series
  refine Finset.sum_congr rfl ?_
  intro r hr
  calc
    (Finset.range N).sum
        (fun n =>
          D.xi_congruence_block_abel_weil_residue_locking_coeff r *
            D.xi_congruence_block_abel_weil_residue_locking_base ^
              ((r : ℕ) + n * D.xi_congruence_block_abel_weil_residue_locking_modulus)) =
      (Finset.range N).sum
        (fun n =>
          D.xi_congruence_block_abel_weil_residue_locking_coeff r *
            D.xi_congruence_block_abel_weil_residue_locking_base ^ (r : ℕ) *
              (D.xi_congruence_block_abel_weil_residue_locking_base ^
                D.xi_congruence_block_abel_weil_residue_locking_modulus) ^ n) := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          calc
            D.xi_congruence_block_abel_weil_residue_locking_coeff r *
                D.xi_congruence_block_abel_weil_residue_locking_base ^
                  ((r : ℕ) + n * D.xi_congruence_block_abel_weil_residue_locking_modulus) =
              D.xi_congruence_block_abel_weil_residue_locking_coeff r *
                (D.xi_congruence_block_abel_weil_residue_locking_base ^ (r : ℕ) *
                  D.xi_congruence_block_abel_weil_residue_locking_base ^
                    (n * D.xi_congruence_block_abel_weil_residue_locking_modulus)) := by
                  rw [pow_add]
            _ =
              D.xi_congruence_block_abel_weil_residue_locking_coeff r *
                (D.xi_congruence_block_abel_weil_residue_locking_base ^ (r : ℕ) *
                  (D.xi_congruence_block_abel_weil_residue_locking_base ^
                    D.xi_congruence_block_abel_weil_residue_locking_modulus) ^ n) := by
                  rw [Nat.mul_comm n
                    D.xi_congruence_block_abel_weil_residue_locking_modulus, pow_mul]
            _ =
              D.xi_congruence_block_abel_weil_residue_locking_coeff r *
                D.xi_congruence_block_abel_weil_residue_locking_base ^ (r : ℕ) *
                  (D.xi_congruence_block_abel_weil_residue_locking_base ^
                    D.xi_congruence_block_abel_weil_residue_locking_modulus) ^ n := by
                      ring
    _ =
      D.xi_congruence_block_abel_weil_residue_locking_coeff r *
          D.xi_congruence_block_abel_weil_residue_locking_base ^ (r : ℕ) *
        (Finset.range N).sum
          (fun n =>
            (D.xi_congruence_block_abel_weil_residue_locking_base ^
              D.xi_congruence_block_abel_weil_residue_locking_modulus) ^ n) := by
          symm
          simpa [mul_assoc] using
            (Finset.mul_sum (Finset.range N)
              (fun n =>
                (D.xi_congruence_block_abel_weil_residue_locking_base ^
                  D.xi_congruence_block_abel_weil_residue_locking_modulus) ^ n)
              (D.xi_congruence_block_abel_weil_residue_locking_coeff r *
                D.xi_congruence_block_abel_weil_residue_locking_base ^ (r : ℕ)))

lemma xi_congruence_block_abel_weil_residue_locking_geometric_kernel
    (D : XiCongruenceBlockAbelWeilResidueLockingData) (N : ℕ) :
    ((Finset.range N).sum fun n =>
        (D.xi_congruence_block_abel_weil_residue_locking_base ^
          D.xi_congruence_block_abel_weil_residue_locking_modulus) ^ n) *
        (D.xi_congruence_block_abel_weil_residue_locking_base ^
          D.xi_congruence_block_abel_weil_residue_locking_modulus - 1) =
      (D.xi_congruence_block_abel_weil_residue_locking_base ^
        D.xi_congruence_block_abel_weil_residue_locking_modulus) ^ N - 1 := by
  simpa using geom_sum_mul
    (D.xi_congruence_block_abel_weil_residue_locking_base ^
      D.xi_congruence_block_abel_weil_residue_locking_modulus) N

lemma xi_congruence_block_abel_weil_residue_locking_common_pole_eq
    (D : XiCongruenceBlockAbelWeilResidueLockingData) :
    1 - D.xi_congruence_block_abel_weil_residue_locking_common_pole *
        D.xi_congruence_block_abel_weil_residue_locking_base ^
          D.xi_congruence_block_abel_weil_residue_locking_modulus = 0 := by
  unfold xi_congruence_block_abel_weil_residue_locking_common_pole
  have hpow :
      D.xi_congruence_block_abel_weil_residue_locking_base ^
        D.xi_congruence_block_abel_weil_residue_locking_modulus ≠ 0 := by
    exact pow_ne_zero _ D.xi_congruence_block_abel_weil_residue_locking_base_ne_zero
  field_simp [hpow]
  ring

lemma xi_congruence_block_abel_weil_residue_locking_residue_formula_eq
    (D : XiCongruenceBlockAbelWeilResidueLockingData)
    (r : Fin D.xi_congruence_block_abel_weil_residue_locking_modulus) :
    D.xi_congruence_block_abel_weil_residue_locking_residue_witness r =
      D.xi_congruence_block_abel_weil_residue_locking_residue_formula r := by
  unfold xi_congruence_block_abel_weil_residue_locking_residue_witness
    xi_congruence_block_abel_weil_residue_locking_residue_formula
    xi_congruence_block_abel_weil_residue_locking_abel_weil_coefficient
    xi_congruence_block_abel_weil_residue_locking_common_pole
  simp [div_eq_mul_inv, mul_left_comm, mul_comm]

end XiCongruenceBlockAbelWeilResidueLockingData

open XiCongruenceBlockAbelWeilResidueLockingData

/-- Paper label: `thm:xi-congruence-block-abel-weil-residue-locking`. -/
theorem paper_xi_congruence_block_abel_weil_residue_locking
    (D : XiCongruenceBlockAbelWeilResidueLockingData) : D.statement := by
  refine ⟨D.xi_congruence_block_abel_weil_residue_locking_grouping,
    D.xi_congruence_block_abel_weil_residue_locking_geometric_kernel,
    D.xi_congruence_block_abel_weil_residue_locking_common_pole_eq, ?_⟩
  intro r
  exact D.xi_congruence_block_abel_weil_residue_locking_residue_formula_eq r

end

end Omega.Zeta
