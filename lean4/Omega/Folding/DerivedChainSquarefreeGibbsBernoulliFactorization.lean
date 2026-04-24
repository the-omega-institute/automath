import Mathlib.Tactic
import Omega.Folding.KilloChainInteriorGodelGcdLcm

namespace Omega.Folding

open scoped BigOperators
open Finset

noncomputable section

/-- Unnormalized Gibbs weight on a free fixed-point subset. -/
def derivedChainSquarefreeWeight {n : ℕ} (z : ℝ) (S : Finset (Fin n)) : ℝ :=
  z ^ S.card

/-- Partition function obtained by summing the squarefree subset weights. -/
def derivedChainSquarefreePartition (n : ℕ) (z : ℝ) : ℝ :=
  ∑ S : Finset (Fin n), derivedChainSquarefreeWeight z S

/-- Moment generating polynomial of the subset-cardinality statistic. -/
def derivedChainSquarefreePgf (n : ℕ) (z t : ℝ) : ℝ :=
  ∑ S : Finset (Fin n), derivedChainSquarefreeWeight z S * t ^ S.card

/-- Normalized Bernoulli mass extracted from the Gibbs fugacity `z`. -/
def derivedChainSquarefreeBernoulliMass (z : ℝ) : ℝ :=
  z / (1 + z)

/-- Normalized PGF of the subset-cardinality statistic. -/
def derivedChainSquarefreeNormalizedPgf (n : ℕ) (z t : ℝ) : ℝ :=
  derivedChainSquarefreePgf n z t / derivedChainSquarefreePartition n z

private lemma derivedChainSquarefreePartition_eq (n : ℕ) (z : ℝ) :
    derivedChainSquarefreePartition n z = (1 + z) ^ n := by
  have h₁ :
      (∑ S : Finset (Fin n), z ^ S.card) =
        Finset.sum ((Finset.univ : Finset (Fin n)).powerset) (fun S => z ^ S.card) := by
    simp
  have h₂ :
      Finset.sum ((Finset.univ : Finset (Fin n)).powerset) (fun S => z ^ S.card) =
        Finset.sum (Finset.range (n + 1)) (fun j => (n.choose j : ℝ) * z ^ j) := by
    simpa [nsmul_eq_mul, Finset.card_univ, mul_comm, mul_left_comm, mul_assoc] using
      (Finset.sum_powerset_apply_card (α := ℝ) (β := Fin n) (f := fun t : ℕ => z ^ t)
        (x := (Finset.univ : Finset (Fin n))))
  have h₃ :
      Finset.sum (Finset.range (n + 1)) (fun j => (n.choose j : ℝ) * z ^ j) = (z + 1) ^ n := by
    simpa [one_pow, mul_one, mul_comm, mul_left_comm, mul_assoc, add_comm] using
      (add_pow z 1 n).symm
  unfold derivedChainSquarefreePartition derivedChainSquarefreeWeight
  rw [h₁, h₂, h₃, add_comm]

private lemma derivedChainSquarefreePgf_eq (n : ℕ) (z t : ℝ) :
    derivedChainSquarefreePgf n z t = (1 + z * t) ^ n := by
  have h₁ :
      (∑ S : Finset (Fin n), z ^ S.card * t ^ S.card) =
        ∑ S : Finset (Fin n), (z * t) ^ S.card := by
    refine Finset.sum_congr rfl ?_
    intro S hS
    rw [← mul_pow]
  have h₂ : (∑ S : Finset (Fin n), (z * t) ^ S.card) = (1 + z * t) ^ n := by
    simpa using derivedChainSquarefreePartition_eq n (z * t)
  unfold derivedChainSquarefreePgf derivedChainSquarefreeWeight
  rw [h₁, h₂]

private lemma derivedChainSquarefree_div_pow (x y : ℝ) (hy : y ≠ 0) (n : ℕ) :
    (x / y) ^ n = x ^ n / y ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [pow_succ, pow_succ, pow_succ, ih]
      field_simp [hy]

/-- Paper label: `thm:derived-chain-squarefree-gibbs-bernoulli-factorization`. The already
verified chain-interior Gödel code identifies the free fixed points with subsets, the resulting
squarefree Gibbs partition function factors as `(1+z)^n`, the normalized cardinality PGF is the
product PGF of `n` Bernoulli coordinates with success probability `z / (1 + z)`, and the
corresponding mean/variance sums are the standard independent Bernoulli formulas. -/
theorem paper_derived_chain_squarefree_gibbs_bernoulli_factorization
    (n : ℕ) (z : ℝ) (hz : 0 < z) :
    ChainInteriorGodelGcdLcm n ∧
      derivedChainSquarefreePartition n z = (1 + z) ^ n ∧
      (∀ t : ℝ,
        derivedChainSquarefreeNormalizedPgf n z t =
          ∏ _i : Fin n,
            (1 - derivedChainSquarefreeBernoulliMass z +
              derivedChainSquarefreeBernoulliMass z * t)) ∧
      (∑ _i : Fin n, derivedChainSquarefreeBernoulliMass z) =
        (n : ℝ) * derivedChainSquarefreeBernoulliMass z ∧
      (∑ _i : Fin n,
          derivedChainSquarefreeBernoulliMass z * (1 - derivedChainSquarefreeBernoulliMass z)) =
        (n : ℝ) *
          (derivedChainSquarefreeBernoulliMass z * (1 - derivedChainSquarefreeBernoulliMass z)) := by
  refine ⟨paper_killo_chain_interior_godel_gcd_lcm n, derivedChainSquarefreePartition_eq n z, ?_, ?_,
    ?_⟩
  · intro t
    have hz1_ne : (1 + z : ℝ) ≠ 0 := by linarith
    have hmass :
        1 - derivedChainSquarefreeBernoulliMass z + derivedChainSquarefreeBernoulliMass z * t =
          (1 + z * t) / (1 + z) := by
      unfold derivedChainSquarefreeBernoulliMass
      field_simp [hz1_ne]
      ring
    calc
      derivedChainSquarefreeNormalizedPgf n z t = (1 + z * t) ^ n / (1 + z) ^ n := by
        unfold derivedChainSquarefreeNormalizedPgf
        rw [derivedChainSquarefreePgf_eq, derivedChainSquarefreePartition_eq]
      _ = ((1 + z * t) / (1 + z)) ^ n := by
        simpa using (derivedChainSquarefree_div_pow (1 + z * t) (1 + z) hz1_ne n).symm
      _ = ∏ i : Fin n, ((1 + z * t) / (1 + z)) := by
        rw [Finset.prod_const]
        simp
      _ = ∏ i : Fin n,
            (1 - derivedChainSquarefreeBernoulliMass z +
              derivedChainSquarefreeBernoulliMass z * t) := by
          refine Finset.prod_congr rfl ?_
          intro i hi
          rw [hmass]
  · simp [derivedChainSquarefreeBernoulliMass]
  · simp [derivedChainSquarefreeBernoulliMass]

end

end Omega.Folding
