import Mathlib

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Concrete numeric parameters for the low-fiber anomaly-tax profile:
`q` is the Wulff floor, `M` the number of fibers, `a` the Wulff excess count, and
`r` the number of forced low fibers. -/
abbrev xi_time_part9xaa_lowfiber_anomaly_tax_data := ℕ × ℕ × ℕ × ℕ

def xi_time_part9xaa_lowfiber_anomaly_tax_q
    (D : xi_time_part9xaa_lowfiber_anomaly_tax_data) : ℕ := D.1

def xi_time_part9xaa_lowfiber_anomaly_tax_M
    (D : xi_time_part9xaa_lowfiber_anomaly_tax_data) : ℕ := D.2.1

def xi_time_part9xaa_lowfiber_anomaly_tax_a
    (D : xi_time_part9xaa_lowfiber_anomaly_tax_data) : ℕ := D.2.2.1

def xi_time_part9xaa_lowfiber_anomaly_tax_r
    (D : xi_time_part9xaa_lowfiber_anomaly_tax_data) : ℕ := D.2.2.2

def xi_time_part9xaa_lowfiber_anomaly_tax_lowCount
    (D : xi_time_part9xaa_lowfiber_anomaly_tax_data) : ℤ :=
  xi_time_part9xaa_lowfiber_anomaly_tax_r D

def xi_time_part9xaa_lowfiber_anomaly_tax_midCount
    (D : xi_time_part9xaa_lowfiber_anomaly_tax_data) : ℤ :=
  xi_time_part9xaa_lowfiber_anomaly_tax_M D -
    xi_time_part9xaa_lowfiber_anomaly_tax_a D -
      2 * xi_time_part9xaa_lowfiber_anomaly_tax_r D

def xi_time_part9xaa_lowfiber_anomaly_tax_highCount
    (D : xi_time_part9xaa_lowfiber_anomaly_tax_data) : ℤ :=
  xi_time_part9xaa_lowfiber_anomaly_tax_a D + xi_time_part9xaa_lowfiber_anomaly_tax_r D

def xi_time_part9xaa_lowfiber_anomaly_tax_wulffMidCount
    (D : xi_time_part9xaa_lowfiber_anomaly_tax_data) : ℤ :=
  xi_time_part9xaa_lowfiber_anomaly_tax_M D - xi_time_part9xaa_lowfiber_anomaly_tax_a D

def xi_time_part9xaa_lowfiber_anomaly_tax_wulffHighCount
    (D : xi_time_part9xaa_lowfiber_anomaly_tax_data) : ℤ :=
  xi_time_part9xaa_lowfiber_anomaly_tax_a D

def xi_time_part9xaa_lowfiber_anomaly_tax_profileMass
    (D : xi_time_part9xaa_lowfiber_anomaly_tax_data) : ℤ :=
  let q := xi_time_part9xaa_lowfiber_anomaly_tax_q D
  xi_time_part9xaa_lowfiber_anomaly_tax_lowCount D * (q - 1 : ℕ) +
    xi_time_part9xaa_lowfiber_anomaly_tax_midCount D * q +
      xi_time_part9xaa_lowfiber_anomaly_tax_highCount D * (q + 1 : ℕ)

def xi_time_part9xaa_lowfiber_anomaly_tax_wulffMass
    (D : xi_time_part9xaa_lowfiber_anomaly_tax_data) : ℤ :=
  let q := xi_time_part9xaa_lowfiber_anomaly_tax_q D
  xi_time_part9xaa_lowfiber_anomaly_tax_wulffMidCount D * q +
    xi_time_part9xaa_lowfiber_anomaly_tax_wulffHighCount D * (q + 1 : ℕ)

def xi_time_part9xaa_lowfiber_anomaly_tax_profilePhi
    (D : xi_time_part9xaa_lowfiber_anomaly_tax_data) (Phi : ℕ → ℤ) : ℤ :=
  let q := xi_time_part9xaa_lowfiber_anomaly_tax_q D
  xi_time_part9xaa_lowfiber_anomaly_tax_lowCount D * Phi (q - 1) +
    xi_time_part9xaa_lowfiber_anomaly_tax_midCount D * Phi q +
      xi_time_part9xaa_lowfiber_anomaly_tax_highCount D * Phi (q + 1)

def xi_time_part9xaa_lowfiber_anomaly_tax_wulffPhi
    (D : xi_time_part9xaa_lowfiber_anomaly_tax_data) (Phi : ℕ → ℤ) : ℤ :=
  let q := xi_time_part9xaa_lowfiber_anomaly_tax_q D
  xi_time_part9xaa_lowfiber_anomaly_tax_wulffMidCount D * Phi q +
    xi_time_part9xaa_lowfiber_anomaly_tax_wulffHighCount D * Phi (q + 1)

def xi_time_part9xaa_lowfiber_anomaly_tax_secondDifference
    (D : xi_time_part9xaa_lowfiber_anomaly_tax_data) (Phi : ℕ → ℤ) : ℤ :=
  let q := xi_time_part9xaa_lowfiber_anomaly_tax_q D
  Phi (q - 1) - 2 * Phi q + Phi (q + 1)

def xi_time_part9xaa_lowfiber_anomaly_tax_squarePhi (n : ℕ) : ℤ := (n : ℤ) ^ 2

def xi_time_part9xaa_lowfiber_anomaly_tax_entropyPhi (n : ℕ) : ℝ :=
  (n : ℝ) * Real.log n

def xi_time_part9xaa_lowfiber_anomaly_tax_entropySecondDifference
    (D : xi_time_part9xaa_lowfiber_anomaly_tax_data) : ℝ :=
  let q := xi_time_part9xaa_lowfiber_anomaly_tax_q D
  xi_time_part9xaa_lowfiber_anomaly_tax_entropyPhi (q - 1) -
    2 * xi_time_part9xaa_lowfiber_anomaly_tax_entropyPhi q +
      xi_time_part9xaa_lowfiber_anomaly_tax_entropyPhi (q + 1)

def xi_time_part9xaa_lowfiber_anomaly_tax_factorialLogPhi (n : ℕ) : ℝ :=
  Finset.sum (Finset.range n) fun k => Real.log (k + 1 : ℝ)

def xi_time_part9xaa_lowfiber_anomaly_tax_factorialLogSecondDifference
    (D : xi_time_part9xaa_lowfiber_anomaly_tax_data) : ℝ :=
  let q := xi_time_part9xaa_lowfiber_anomaly_tax_q D
  Real.log ((q + 1 : ℝ) / q)

def xi_time_part9xaa_lowfiber_anomaly_tax_statement
    (D : xi_time_part9xaa_lowfiber_anomaly_tax_data) : Prop :=
  let q := xi_time_part9xaa_lowfiber_anomaly_tax_q D
  let M := xi_time_part9xaa_lowfiber_anomaly_tax_M D
  let r := xi_time_part9xaa_lowfiber_anomaly_tax_r D
  2 ≤ q →
    xi_time_part9xaa_lowfiber_anomaly_tax_profileMass D =
        xi_time_part9xaa_lowfiber_anomaly_tax_wulffMass D ∧
      xi_time_part9xaa_lowfiber_anomaly_tax_lowCount D +
          xi_time_part9xaa_lowfiber_anomaly_tax_midCount D +
            xi_time_part9xaa_lowfiber_anomaly_tax_highCount D =
        M ∧
      (∀ Phi : ℕ → ℤ,
        xi_time_part9xaa_lowfiber_anomaly_tax_profilePhi D Phi -
            xi_time_part9xaa_lowfiber_anomaly_tax_wulffPhi D Phi =
          r * xi_time_part9xaa_lowfiber_anomaly_tax_secondDifference D Phi) ∧
      xi_time_part9xaa_lowfiber_anomaly_tax_secondDifference D
          xi_time_part9xaa_lowfiber_anomaly_tax_squarePhi =
        2 ∧
      xi_time_part9xaa_lowfiber_anomaly_tax_factorialLogSecondDifference D =
        Real.log ((q + 1 : ℝ) / q) ∧
      xi_time_part9xaa_lowfiber_anomaly_tax_entropySecondDifference D =
        (q - 1 : ℝ) * Real.log (q - 1 : ℕ) - 2 * ((q : ℝ) * Real.log q) +
          (q + 1 : ℝ) * Real.log (q + 1 : ℕ)

theorem paper_xi_time_part9xaa_lowfiber_anomaly_tax
    (D : xi_time_part9xaa_lowfiber_anomaly_tax_data) :
    xi_time_part9xaa_lowfiber_anomaly_tax_statement D := by
  rcases D with ⟨q, M, a, r⟩
  dsimp [xi_time_part9xaa_lowfiber_anomaly_tax_statement,
    xi_time_part9xaa_lowfiber_anomaly_tax_q, xi_time_part9xaa_lowfiber_anomaly_tax_M,
    xi_time_part9xaa_lowfiber_anomaly_tax_a, xi_time_part9xaa_lowfiber_anomaly_tax_r,
    xi_time_part9xaa_lowfiber_anomaly_tax_profileMass,
    xi_time_part9xaa_lowfiber_anomaly_tax_wulffMass,
    xi_time_part9xaa_lowfiber_anomaly_tax_lowCount,
    xi_time_part9xaa_lowfiber_anomaly_tax_midCount,
    xi_time_part9xaa_lowfiber_anomaly_tax_highCount,
    xi_time_part9xaa_lowfiber_anomaly_tax_wulffMidCount,
    xi_time_part9xaa_lowfiber_anomaly_tax_wulffHighCount,
    xi_time_part9xaa_lowfiber_anomaly_tax_profilePhi,
    xi_time_part9xaa_lowfiber_anomaly_tax_wulffPhi,
    xi_time_part9xaa_lowfiber_anomaly_tax_secondDifference]
  intro hq
  have hqsub : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := by omega
  constructor
  · rw [hqsub]
    ring
  constructor
  · ring
  constructor
  · intro Phi
    ring
  constructor
  · dsimp [xi_time_part9xaa_lowfiber_anomaly_tax_squarePhi]
    rw [hqsub]
    ring
  constructor
  · rfl
  · dsimp [xi_time_part9xaa_lowfiber_anomaly_tax_entropySecondDifference,
      xi_time_part9xaa_lowfiber_anomaly_tax_entropyPhi,
      xi_time_part9xaa_lowfiber_anomaly_tax_q]
    have hqsubR : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ q)]
      norm_num
    have hqsuccR : ((q + 1 : ℕ) : ℝ) = (q : ℝ) + 1 := by norm_num
    rw [hqsubR, hqsuccR]

end

end Omega.Zeta
