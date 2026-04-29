import Mathlib.NumberTheory.Real.GoldenRatio
import Omega.Folding.Entropy
import Omega.Zeta.XiZgAddressBinarySelfAffine

open Filter Topology
open scoped goldenRatio

namespace Omega.Zeta

/-- Finite no-adjacent-one ZG prefixes of length `n`. -/
def xi_zg_address_minkowski_dimension_content_finite_admissible_prefix
    (n : ℕ) (w : Fin n → Bool) : Prop :=
  ∀ i : Fin n, ∀ hnext : i.1 + 1 < n,
    w i = true → w ⟨i.1 + 1, hnext⟩ = false

/-- Fibonacci prefix count for the finite ZG no-adjacent-one language. -/
def xi_zg_address_minkowski_dimension_content_prefix_count : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | n + 2 =>
      xi_zg_address_minkowski_dimension_content_prefix_count (n + 1) +
        xi_zg_address_minkowski_dimension_content_prefix_count n

/-- The prefix count satisfies the Fibonacci two-step recurrence. -/
lemma xi_zg_address_minkowski_dimension_content_prefix_count_recurrence (n : ℕ) :
    xi_zg_address_minkowski_dimension_content_prefix_count (n + 2) =
      xi_zg_address_minkowski_dimension_content_prefix_count (n + 1) +
        xi_zg_address_minkowski_dimension_content_prefix_count n := by
  rfl

/-- The finite ZG prefix count is `F_{n+2}`. -/
lemma xi_zg_address_minkowski_dimension_content_prefix_count_eq_fib :
    ∀ n : ℕ,
      xi_zg_address_minkowski_dimension_content_prefix_count n = Nat.fib (n + 2) := by
  refine Nat.twoStepInduction ?_ ?_ ?_
  · simp [xi_zg_address_minkowski_dimension_content_prefix_count, Nat.fib]
  · simp [xi_zg_address_minkowski_dimension_content_prefix_count, Nat.fib]
  · intro n hn hn1
    calc
      xi_zg_address_minkowski_dimension_content_prefix_count (n + 2)
          =
            xi_zg_address_minkowski_dimension_content_prefix_count (n + 1) +
              xi_zg_address_minkowski_dimension_content_prefix_count n := by
            rw [xi_zg_address_minkowski_dimension_content_prefix_count_recurrence]
      _ = Nat.fib (n + 3) + Nat.fib (n + 2) := by rw [hn1, hn]
      _ = Nat.fib (n + 4) := by
            have hfib :
                Nat.fib (n + 4) = Nat.fib (n + 2) + Nat.fib (n + 3) := by
              rw [show n + 4 = (n + 2) + 2 by omega, Nat.fib_add_two]
            rw [hfib]
            exact Nat.add_comm _ _

/-- Natural-scale cylinder covering count. -/
def xi_zg_address_minkowski_dimension_content_cover_count (_L n : ℕ) : ℕ :=
  xi_zg_address_minkowski_dimension_content_prefix_count n

/-- The symbolic Minkowski dimension attached to the natural `2^L`-adic scale. -/
noncomputable def xi_zg_address_minkowski_dimension_content_dimension (L : ℕ) : ℝ :=
  Real.log φ / Real.log ((2 ^ L : ℕ) : ℝ)

/-- Natural-scale content after substituting `B^s = φ`. -/
noncomputable def xi_zg_address_minkowski_dimension_content_natural_content (n : ℕ) : ℝ :=
  (xi_zg_address_minkowski_dimension_content_prefix_count n : ℝ) * φ ^ (-(n : ℝ))

/-- Concrete local package for the ZG address covering count, dimension, and natural content. -/
def xi_zg_address_minkowski_dimension_content_statement (L : ℕ) : Prop :=
  xi_zg_address_binary_self_affine_statement L ∧
    (∀ n : ℕ,
      xi_zg_address_minkowski_dimension_content_cover_count L n = Nat.fib (n + 2)) ∧
    (∀ n : ℕ,
      xi_zg_address_minkowski_dimension_content_prefix_count (n + 2) =
        xi_zg_address_minkowski_dimension_content_prefix_count (n + 1) +
          xi_zg_address_minkowski_dimension_content_prefix_count n) ∧
    xi_zg_address_minkowski_dimension_content_dimension L =
      Real.log φ / Real.log ((2 ^ L : ℕ) : ℝ) ∧
    xi_zg_address_minkowski_dimension_content_dimension L =
      Real.log φ / ((L : ℝ) * Real.log 2) ∧
    Tendsto xi_zg_address_minkowski_dimension_content_natural_content atTop
      (nhds (φ ^ (2 : ℕ) / Real.sqrt 5))

/-- Paper label: `thm:xi-zg-address-minkowski-dimension-content`. -/
theorem paper_xi_zg_address_minkowski_dimension_content (L : Nat) (hL : 1 ≤ L) :
    xi_zg_address_minkowski_dimension_content_statement L := by
  refine ⟨paper_xi_zg_address_binary_self_affine L hL, ?_, ?_, rfl, ?_, ?_⟩
  · intro n
    exact xi_zg_address_minkowski_dimension_content_prefix_count_eq_fib n
  · exact xi_zg_address_minkowski_dimension_content_prefix_count_recurrence
  · unfold xi_zg_address_minkowski_dimension_content_dimension
    have hcast : (((2 ^ L : ℕ) : ℝ)) = (2 : ℝ) ^ L := by norm_num
    rw [hcast, Real.log_pow]
  · have hshift :=
      Omega.Entropy.fib_mul_phi_neg_tendsto_inv_sqrt5.comp (tendsto_add_atTop_nat 2)
    have hmul :
        Tendsto
          (fun n : ℕ => ((Nat.fib (n + 2) : ℝ) * φ ^ (-(n + 2 : ℝ))) * φ ^ (2 : ℕ))
          atTop (nhds ((Real.sqrt 5)⁻¹ * φ ^ (2 : ℕ))) := by
      simpa [Function.comp] using hshift.mul tendsto_const_nhds
    have hevent :
        (fun n : ℕ => xi_zg_address_minkowski_dimension_content_natural_content n) =ᶠ[atTop]
          fun n => ((Nat.fib (n + 2) : ℝ) * φ ^ (-(n + 2 : ℝ))) * φ ^ (2 : ℕ) :=
      Filter.Eventually.of_forall fun n => by
        unfold xi_zg_address_minkowski_dimension_content_natural_content
        have hpow :
            φ ^ (-(n : ℝ)) = φ ^ (-(n + 2 : ℝ)) * φ ^ (2 : ℝ) := by
          rw [show (-(n : ℝ)) = (-(n + 2 : ℝ)) + (2 : ℝ) by norm_num]
          exact Real.rpow_add Real.goldenRatio_pos (-(n + 2 : ℝ)) (2 : ℝ)
        calc
          (xi_zg_address_minkowski_dimension_content_prefix_count n : ℝ) * φ ^ (-(n : ℝ))
              = (Nat.fib (n + 2) : ℝ) * φ ^ (-(n : ℝ)) := by
                  rw [xi_zg_address_minkowski_dimension_content_prefix_count_eq_fib n]
          _ = (Nat.fib (n + 2) : ℝ) * (φ ^ (-(n + 2 : ℝ)) * φ ^ (2 : ℕ)) := by
                  simpa [Real.rpow_natCast] using
                    congrArg ((Nat.fib (n + 2) : ℝ) * ·) hpow
          _ = ((Nat.fib (n + 2) : ℝ) * φ ^ (-(n + 2 : ℝ))) * φ ^ (2 : ℕ) := by
                ring
    refine Filter.Tendsto.congr' hevent.symm ?_
    simpa [one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul

end Omega.Zeta
