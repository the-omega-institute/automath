import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Concrete finite atomic data for the scan-fingerprint Caratheodory lift.  Each atom has a
positive weight and a radius in the open unit disk, so its Cayley contribution has positive real
part and its Taylor coefficients are the finite moment sums. -/
structure xi_scan_fingerprint_caratheodory_lift_data where
  xi_scan_fingerprint_caratheodory_lift_atomCount : ℕ
  xi_scan_fingerprint_caratheodory_lift_weight :
    Fin xi_scan_fingerprint_caratheodory_lift_atomCount → ℝ
  xi_scan_fingerprint_caratheodory_lift_radius :
    Fin xi_scan_fingerprint_caratheodory_lift_atomCount → ℝ
  xi_scan_fingerprint_caratheodory_lift_atomCount_pos :
    0 < xi_scan_fingerprint_caratheodory_lift_atomCount
  xi_scan_fingerprint_caratheodory_lift_weight_pos :
    ∀ i, 0 < xi_scan_fingerprint_caratheodory_lift_weight i
  xi_scan_fingerprint_caratheodory_lift_radius_nonneg :
    ∀ i, 0 ≤ xi_scan_fingerprint_caratheodory_lift_radius i
  xi_scan_fingerprint_caratheodory_lift_radius_lt_one :
    ∀ i, xi_scan_fingerprint_caratheodory_lift_radius i < 1

namespace xi_scan_fingerprint_caratheodory_lift_data

/-- The Cayley right-half-plane summand attached to one disk atom. -/
def cayleyTerm (D : xi_scan_fingerprint_caratheodory_lift_data)
    (i : Fin D.xi_scan_fingerprint_caratheodory_lift_atomCount) : ℝ :=
  D.xi_scan_fingerprint_caratheodory_lift_weight i *
    ((1 + D.xi_scan_fingerprint_caratheodory_lift_radius i) /
      (1 - D.xi_scan_fingerprint_caratheodory_lift_radius i))

/-- The `k`th Taylor coefficient of the finite Carathéodory lift. -/
def taylorCoefficient (D : xi_scan_fingerprint_caratheodory_lift_data) (k : ℕ) : ℝ :=
  ∑ i : Fin D.xi_scan_fingerprint_caratheodory_lift_atomCount,
    D.xi_scan_fingerprint_caratheodory_lift_weight i *
      D.xi_scan_fingerprint_caratheodory_lift_radius i ^ k

/-- The contribution of one atom to the first `n` Taylor coefficients. -/
def atomGeometricPartial (D : xi_scan_fingerprint_caratheodory_lift_data)
    (i : Fin D.xi_scan_fingerprint_caratheodory_lift_atomCount) (n : ℕ) : ℝ :=
  D.xi_scan_fingerprint_caratheodory_lift_weight i *
    ∑ k ∈ Finset.range n, D.xi_scan_fingerprint_caratheodory_lift_radius i ^ k

/-- The atom-first finite geometric expansion. -/
def atomFirstPartial (D : xi_scan_fingerprint_caratheodory_lift_data) (n : ℕ) : ℝ :=
  ∑ i : Fin D.xi_scan_fingerprint_caratheodory_lift_atomCount, D.atomGeometricPartial i n

/-- The coefficient-first finite Taylor expansion. -/
def coefficientFirstPartial (D : xi_scan_fingerprint_caratheodory_lift_data) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, D.taylorCoefficient k

/-- The Cayley lift has strictly positive right-half-plane real part at the scan point. -/
def strictRightHalfPlanePositive
    (D : xi_scan_fingerprint_caratheodory_lift_data) : Prop :=
  0 < ∑ i : Fin D.xi_scan_fingerprint_caratheodory_lift_atomCount, D.cayleyTerm i

/-- Finite geometric-series expansion recovers exactly the Taylor coefficient package. -/
def taylorCoefficientRecovery
    (D : xi_scan_fingerprint_caratheodory_lift_data) : Prop :=
  ∀ n, D.atomFirstPartial n = D.coefficientFirstPartial n

/-- The fingerprint coefficients are precisely the finite weighted moment sequence. -/
def fingerprintEquivalence
    (D : xi_scan_fingerprint_caratheodory_lift_data) : Prop :=
  ∀ k,
    D.taylorCoefficient k =
      ∑ i : Fin D.xi_scan_fingerprint_caratheodory_lift_atomCount,
        D.xi_scan_fingerprint_caratheodory_lift_weight i *
          D.xi_scan_fingerprint_caratheodory_lift_radius i ^ k

end xi_scan_fingerprint_caratheodory_lift_data

open xi_scan_fingerprint_caratheodory_lift_data

/-- Paper label: `prop:xi-scan-fingerprint-caratheodory-lift`. -/
theorem paper_xi_scan_fingerprint_caratheodory_lift
    (D : xi_scan_fingerprint_caratheodory_lift_data) :
    D.strictRightHalfPlanePositive ∧ D.taylorCoefficientRecovery ∧ D.fingerprintEquivalence := by
  refine ⟨?_, ?_, ?_⟩
  · refine Finset.sum_pos ?_ ?_
    · intro i _
      have hden : 0 < 1 - D.xi_scan_fingerprint_caratheodory_lift_radius i := by
        linarith [D.xi_scan_fingerprint_caratheodory_lift_radius_lt_one i]
      have hnum : 0 < 1 + D.xi_scan_fingerprint_caratheodory_lift_radius i := by
        linarith [D.xi_scan_fingerprint_caratheodory_lift_radius_nonneg i]
      exact mul_pos (D.xi_scan_fingerprint_caratheodory_lift_weight_pos i)
        (div_pos hnum hden)
    · exact ⟨⟨0, D.xi_scan_fingerprint_caratheodory_lift_atomCount_pos⟩, Finset.mem_univ _⟩
  · intro n
    calc
      D.atomFirstPartial n =
          ∑ i : Fin D.xi_scan_fingerprint_caratheodory_lift_atomCount,
            ∑ k ∈ Finset.range n,
              D.xi_scan_fingerprint_caratheodory_lift_weight i *
                D.xi_scan_fingerprint_caratheodory_lift_radius i ^ k := by
            simp [atomFirstPartial, atomGeometricPartial, Finset.mul_sum]
      _ = ∑ k ∈ Finset.range n,
            ∑ i : Fin D.xi_scan_fingerprint_caratheodory_lift_atomCount,
              D.xi_scan_fingerprint_caratheodory_lift_weight i *
                D.xi_scan_fingerprint_caratheodory_lift_radius i ^ k := by
            rw [Finset.sum_comm]
      _ = D.coefficientFirstPartial n := by
            simp [coefficientFirstPartial, taylorCoefficient]
  · intro k
    rfl

end

end Omega.Zeta
