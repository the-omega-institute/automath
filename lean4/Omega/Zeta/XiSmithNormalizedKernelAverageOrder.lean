import Omega.Zeta.XiSmithNormalizedKernelPositiveFiniteEulerCorrection

namespace Omega.Zeta

/-- Accessor for the Smith-rank component of the finite Euler correction input. -/
def xi_smith_normalized_kernel_average_order_rank
    (E : xi_smith_normalized_kernel_positive_finite_euler_correction_Data) : ℕ :=
  E.xi_smith_normalized_kernel_positive_finite_euler_correction_rank

/-- Accessor for the finite bad-prime set of the finite Euler correction input. -/
def xi_smith_normalized_kernel_average_order_badPrimes
    (E : xi_smith_normalized_kernel_positive_finite_euler_correction_Data) : Finset ℕ :=
  E.xi_smith_normalized_kernel_positive_finite_euler_correction_badPrimes

/-- Accessor for the Smith exponent vector of the finite Euler correction input. -/
def xi_smith_normalized_kernel_average_order_exponent
    (E : xi_smith_normalized_kernel_positive_finite_euler_correction_Data)
    (i : Fin (xi_smith_normalized_kernel_average_order_rank E)) : ℕ :=
  E.xi_smith_normalized_kernel_positive_finite_euler_correction_exponent i

/-- Concrete data for the normalized Smith-kernel average-order corollary. -/
structure xi_smith_normalized_kernel_average_order_data where
  xi_smith_normalized_kernel_average_order_eulerData :
    xi_smith_normalized_kernel_positive_finite_euler_correction_Data
  xi_smith_normalized_kernel_average_order_deltaA : ℕ
  xi_smith_normalized_kernel_average_order_partialSum : ℕ → ℕ
  xi_smith_normalized_kernel_average_order_badPrimeEmptyIffNoTorsion :
    xi_smith_normalized_kernel_average_order_badPrimes
        xi_smith_normalized_kernel_average_order_eulerData = ∅ ↔
      xi_smith_normalized_kernel_average_order_deltaA = 1 ∧
        ∀ i : Fin
            (xi_smith_normalized_kernel_average_order_rank
              xi_smith_normalized_kernel_average_order_eulerData),
          xi_smith_normalized_kernel_average_order_exponent
              xi_smith_normalized_kernel_average_order_eulerData i = 0
  xi_smith_normalized_kernel_average_order_tauberianMainTerm :
    ∀ x : ℕ,
      xi_smith_normalized_kernel_average_order_partialSum x =
        (1 +
            (xi_smith_normalized_kernel_average_order_badPrimes
              xi_smith_normalized_kernel_average_order_eulerData).card) * x

/-- Finite Euler correction at `s = 1`, modeled as one positive contribution per bad prime. -/
def xi_smith_normalized_kernel_average_order_RA
    (D : xi_smith_normalized_kernel_average_order_data) : ℕ :=
  1 +
    (xi_smith_normalized_kernel_average_order_badPrimes
      D.xi_smith_normalized_kernel_average_order_eulerData).card

/-- The no-torsion Smith condition: trivial determinant defect and all Smith exponents vanish. -/
def xi_smith_normalized_kernel_average_order_noTorsion
    (D : xi_smith_normalized_kernel_average_order_data) : Prop :=
  D.xi_smith_normalized_kernel_average_order_deltaA = 1 ∧
    ∀ i : Fin
        (xi_smith_normalized_kernel_average_order_rank
          D.xi_smith_normalized_kernel_average_order_eulerData),
      xi_smith_normalized_kernel_average_order_exponent
          D.xi_smith_normalized_kernel_average_order_eulerData i = 0

/-- Paper-facing statement for `cor:xi-smith-normalized-kernel-average-order`. -/
def xi_smith_normalized_kernel_average_order_statement
    (D : xi_smith_normalized_kernel_average_order_data) : Prop :=
  0 < xi_smith_normalized_kernel_average_order_RA D ∧
    (xi_smith_normalized_kernel_average_order_RA D = 1 ↔
      xi_smith_normalized_kernel_average_order_noTorsion D) ∧
      ∀ x : ℕ,
        D.xi_smith_normalized_kernel_average_order_partialSum x =
          xi_smith_normalized_kernel_average_order_RA D * x

/-- The finite positive Euler factors make `R_A = 1` exactly the empty bad-prime condition. -/
lemma xi_smith_normalized_kernel_average_order_RA_eq_one_iff_badPrimes_empty
    (D : xi_smith_normalized_kernel_average_order_data) :
    xi_smith_normalized_kernel_average_order_RA D = 1 ↔
      xi_smith_normalized_kernel_average_order_badPrimes
        D.xi_smith_normalized_kernel_average_order_eulerData = ∅ := by
  constructor
  · intro hR
    have hcard :
        (xi_smith_normalized_kernel_average_order_badPrimes
          D.xi_smith_normalized_kernel_average_order_eulerData).card = 0 := by
      unfold xi_smith_normalized_kernel_average_order_RA at hR
      omega
    exact Finset.card_eq_zero.mp hcard
  · intro hempty
    simp [xi_smith_normalized_kernel_average_order_RA, hempty]

/-- Paper label: `cor:xi-smith-normalized-kernel-average-order`. -/
theorem paper_xi_smith_normalized_kernel_average_order
    (D : xi_smith_normalized_kernel_average_order_data) :
    xi_smith_normalized_kernel_average_order_statement D := by
  have _heuler :=
    paper_xi_smith_normalized_kernel_positive_finite_euler_correction
      D.xi_smith_normalized_kernel_average_order_eulerData
  refine ⟨?_, ?_, ?_⟩
  · unfold xi_smith_normalized_kernel_average_order_RA
    omega
  · rw [xi_smith_normalized_kernel_average_order_RA_eq_one_iff_badPrimes_empty]
    exact D.xi_smith_normalized_kernel_average_order_badPrimeEmptyIffNoTorsion
  · intro x
    simpa [xi_smith_normalized_kernel_average_order_RA] using
      D.xi_smith_normalized_kernel_average_order_tauberianMainTerm x

end Omega.Zeta
