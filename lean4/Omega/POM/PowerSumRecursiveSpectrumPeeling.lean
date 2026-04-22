import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.POM

/-- Concrete finite-spectrum data for recursive peeling of a power-sum expansion. The functions
`coeff` and `root` are indexed by `ℕ`, but the support of `coeff` is truncated at `order`, so the
power sums are genuinely finite exponential sums. -/
structure PomPowerSumRecursiveSpectrumPeelingData where
  order : ℕ
  coeff : ℕ → ℝ
  root : ℕ → ℝ
  θ : ℝ
  coeff_nonneg : ∀ j, 0 ≤ coeff j
  coeff_zero_of_ge : ∀ j, order ≤ j → coeff j = 0
  root_nonneg : ∀ j, 0 ≤ root j
  root_le_theta : ∀ j, root j ≤ θ
  theta_nonneg : 0 ≤ θ

namespace PomPowerSumRecursiveSpectrumPeelingData

def spectralTerm (D : PomPowerSumRecursiveSpectrumPeelingData) (j q : ℕ) : ℝ :=
  D.coeff j * D.root j ^ q

def powerSum (D : PomPowerSumRecursiveSpectrumPeelingData) (q : ℕ) : ℝ :=
  Finset.sum (Finset.range D.order) (fun j => D.spectralTerm j q)

def residual (D : PomPowerSumRecursiveSpectrumPeelingData) : ℕ → ℕ → ℝ
  | 0, q => D.powerSum q
  | k + 1, q => D.residual k q - D.spectralTerm k q

def exactPowerSumExpansion (D : PomPowerSumRecursiveSpectrumPeelingData) : Prop :=
  ∀ q, D.residual 0 q = Finset.sum (Finset.range D.order) (fun j => D.spectralTerm j q)

def recursivePeelingRecovery (D : PomPowerSumRecursiveSpectrumPeelingData) : Prop :=
  ∀ k q, D.residual k q = Finset.sum (Finset.range (D.order - k)) (fun j => D.spectralTerm (k + j) q)

def exponentialConvergence (D : PomPowerSumRecursiveSpectrumPeelingData) : Prop :=
  ∀ k q, D.residual k q ≤ Finset.sum (Finset.range D.order) (fun j => D.coeff j * D.θ ^ q)

end PomPowerSumRecursiveSpectrumPeelingData

open PomPowerSumRecursiveSpectrumPeelingData

theorem paper_pom_power_sum_recursive_spectrum_peeling
    (D : PomPowerSumRecursiveSpectrumPeelingData) :
    D.exactPowerSumExpansion ∧ D.recursivePeelingRecovery ∧ D.exponentialConvergence := by
  have hpow_le :
      ∀ j q, D.coeff j * D.root j ^ q ≤ D.coeff j * D.θ ^ q := by
    intro j q
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (D.root_nonneg j) (D.root_le_theta j) q)
      (D.coeff_nonneg j)
  have hterm_nonneg : ∀ j q, 0 ≤ D.spectralTerm j q := by
    intro j q
    exact mul_nonneg (D.coeff_nonneg j) (pow_nonneg (D.root_nonneg j) q)
  have hexact : D.exactPowerSumExpansion := by
    dsimp [PomPowerSumRecursiveSpectrumPeelingData.exactPowerSumExpansion]
    intro q
    rfl
  have hrecursive : D.recursivePeelingRecovery := by
    dsimp [PomPowerSumRecursiveSpectrumPeelingData.recursivePeelingRecovery]
    intro k q
    induction k with
    | zero =>
        simp [PomPowerSumRecursiveSpectrumPeelingData.residual,
          PomPowerSumRecursiveSpectrumPeelingData.powerSum]
    | succ k ih =>
        by_cases hk : k < D.order
        · have hsub : D.order - k = D.order - (k + 1) + 1 := by
            omega
          calc
            D.residual (k + 1) q
                = D.residual k q - D.spectralTerm k q := by
                    simp [PomPowerSumRecursiveSpectrumPeelingData.residual]
            _ = Finset.sum (Finset.range (D.order - k)) (fun j => D.spectralTerm (k + j) q) -
                  D.spectralTerm k q := by
                    rw [ih]
            _ = (D.spectralTerm k q +
                  Finset.sum (Finset.range (D.order - (k + 1)))
                    (fun j => D.spectralTerm (k + 1 + j) q)) -
                  D.spectralTerm k q := by
                    rw [hsub, Finset.sum_range_succ']
                    simp [add_left_comm, add_comm]
            _ = Finset.sum (Finset.range (D.order - (k + 1)))
                  (fun j => D.spectralTerm (k + 1 + j) q) := by
                    ring
        · have hk' : D.order ≤ k := Nat.not_lt.mp hk
          have hk0 : D.spectralTerm k q = 0 := by
            unfold PomPowerSumRecursiveSpectrumPeelingData.spectralTerm
            rw [D.coeff_zero_of_ge k hk']
            simp
          have hk1 : D.order - (k + 1) = 0 := by
            omega
          calc
            D.residual (k + 1) q = D.residual k q - D.spectralTerm k q := by
              simp [PomPowerSumRecursiveSpectrumPeelingData.residual]
            _ = D.residual k q := by rw [hk0, sub_zero]
            _ = Finset.sum (Finset.range (D.order - k)) (fun j => D.spectralTerm (k + j) q) := ih
            _ = 0 := by simp [Nat.sub_eq_zero_of_le hk']
            _ = Finset.sum (Finset.range (D.order - (k + 1)))
                  (fun j => D.spectralTerm (k + 1 + j) q) := by
              simp [hk1]
  have hbase_bound :
      ∀ q, D.residual 0 q ≤ Finset.sum (Finset.range D.order) (fun j => D.coeff j * D.θ ^ q) := by
    intro q
    calc
      D.residual 0 q = Finset.sum (Finset.range D.order) (fun j => D.spectralTerm j q) := by
        simp [PomPowerSumRecursiveSpectrumPeelingData.residual,
          PomPowerSumRecursiveSpectrumPeelingData.powerSum]
      _ ≤ Finset.sum (Finset.range D.order) (fun j => D.coeff j * D.θ ^ q) := by
        refine Finset.sum_le_sum ?_
        intro j hj
        exact hpow_le j q
  have hbound : D.exponentialConvergence := by
    dsimp [PomPowerSumRecursiveSpectrumPeelingData.exponentialConvergence]
    intro k q
    induction k with
    | zero =>
        exact hbase_bound q
    | succ k ih =>
        calc
          D.residual (k + 1) q = D.residual k q - D.spectralTerm k q := by
            simp [PomPowerSumRecursiveSpectrumPeelingData.residual]
          _ ≤ D.residual k q := sub_le_self _ (hterm_nonneg k q)
          _ ≤ Finset.sum (Finset.range D.order) (fun j => D.coeff j * D.θ ^ q) := ih
  exact ⟨hexact, hrecursive, hbound⟩

end Omega.POM
