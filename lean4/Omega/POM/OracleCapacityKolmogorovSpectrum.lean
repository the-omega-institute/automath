import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.POM

universe u

/-- Concrete finite-output data for the aggregate comparison between oracle capacity and the
conditional Kolmogorov description spectrum. The function `kolmogorovCount x B` records how many
points in the fiber over `x` admit a description of length at most `B`, while `fiberContainment`
keeps that count inside the ambient finite fiber size. -/
structure OracleCapacityKolmogorovSpectrumData where
  X : Type u
  instFintypeX : Fintype X
  fiberCardinality : X → ℕ
  kolmogorovCount : X → ℕ → ℕ
  fiberContainment : ∀ x B, kolmogorovCount x B ≤ fiberCardinality x

attribute [instance] OracleCapacityKolmogorovSpectrumData.instFintypeX

namespace OracleCapacityKolmogorovSpectrumData

/-- Prefix-free counting bounds the number of fiber points with conditional Kolmogorov complexity
at most `B` by `2^B`. -/
def pointwiseKolmogorovBound (D : OracleCapacityKolmogorovSpectrumData) : Prop :=
  ∀ x B, D.kolmogorovCount x B ≤ 2 ^ B

/-- An explicit enumeration/unranking scheme with constant overhead `c` covers
`min(d_f(x), 2^B)` points in every fiber using descriptions of length `B + c`. -/
def pointwiseCapacityCoverage (D : OracleCapacityKolmogorovSpectrumData) : Prop :=
  ∃ c, ∀ x B, Nat.min (D.fiberCardinality x) (2 ^ B) ≤ D.kolmogorovCount x (B + c)

/-- Summing the pointwise lower and upper comparisons over the output fibers yields a single
aggregate comparison with the same constant overhead `c`. -/
def aggregateSpectrumEquivalence (D : OracleCapacityKolmogorovSpectrumData) : Prop :=
  ∃ c, ∀ B,
    (∑ x, Nat.min (D.fiberCardinality x) (2 ^ B)) ≤
        ∑ x, D.kolmogorovCount x (B + c) ∧
      (∑ x, D.kolmogorovCount x (B + c)) ≤
        2 ^ c * ∑ x, Nat.min (D.fiberCardinality x) (2 ^ B)

lemma pointwise_min_bound (D : OracleCapacityKolmogorovSpectrumData)
    (hPointwise : D.pointwiseKolmogorovBound) (x : D.X) (B : ℕ) :
    D.kolmogorovCount x B ≤ Nat.min (D.fiberCardinality x) (2 ^ B) := by
  exact le_min (D.fiberContainment x B) (hPointwise x B)

private lemma min_pow_shift_le (d B c : ℕ) :
    Nat.min d (2 ^ (B + c)) ≤ 2 ^ c * Nat.min d (2 ^ B) := by
  by_cases h : d ≤ 2 ^ B
  · have hmin : Nat.min d (2 ^ B) = d := Nat.min_eq_left h
    calc
      Nat.min d (2 ^ (B + c)) ≤ d := Nat.min_le_left _ _
      _ = 1 * d := by simp
      _ ≤ 2 ^ c * d := by
        have hpow : 0 < 2 ^ c := by
          exact pow_pos (by decide : 0 < 2) _
        exact Nat.mul_le_mul_right d (Nat.succ_le_of_lt hpow)
      _ = 2 ^ c * Nat.min d (2 ^ B) := by rw [hmin]
  · have h' : 2 ^ B ≤ d := Nat.le_of_lt (lt_of_not_ge h)
    have hmin : Nat.min d (2 ^ B) = 2 ^ B := Nat.min_eq_right h'
    calc
      Nat.min d (2 ^ (B + c)) ≤ 2 ^ (B + c) := Nat.min_le_right _ _
      _ = 2 ^ B * 2 ^ c := by rw [Nat.pow_add]
      _ = 2 ^ c * Nat.min d (2 ^ B) := by rw [hmin, Nat.mul_comm]

end OracleCapacityKolmogorovSpectrumData

open OracleCapacityKolmogorovSpectrumData

/-- Paper label: `thm:pom-oracle-capacity-kolmogorov-spectrum`. -/
theorem paper_pom_oracle_capacity_kolmogorov_spectrum
    (D : OracleCapacityKolmogorovSpectrumData) :
    D.pointwiseKolmogorovBound →
      D.pointwiseCapacityCoverage →
        D.aggregateSpectrumEquivalence := by
  intro hPointwise hCoverage
  rcases hCoverage with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro B
  constructor
  · exact Finset.sum_le_sum (fun x _ => hc x B)
  · calc
      ∑ x, D.kolmogorovCount x (B + c) ≤
          ∑ x, 2 ^ c * Nat.min (D.fiberCardinality x) (2 ^ B) := by
            exact Finset.sum_le_sum (fun x _ => by
              have hMin :
                  D.kolmogorovCount x (B + c) ≤
                    Nat.min (D.fiberCardinality x) (2 ^ (B + c)) :=
                D.pointwise_min_bound hPointwise x (B + c)
              exact le_trans hMin
                (OracleCapacityKolmogorovSpectrumData.min_pow_shift_le
                  (D.fiberCardinality x) B c))
      _ = 2 ^ c * ∑ x, Nat.min (D.fiberCardinality x) (2 ^ B) := by
          rw [Finset.mul_sum]

end Omega.POM
