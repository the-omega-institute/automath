import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.Zeta.XiPickPoissonPrincipalMinorsPartition

open scoped BigOperators

namespace Omega.Zeta

/-- The per-index weight contributing to each principal minor in the abstract Pick--Poisson
product model. -/
def xiPickPoissonIndexWeight {kappa : Nat} (P : XiPickPoissonGram kappa) (i : Fin kappa) : ℝ :=
  P.pointWeight i * P.kernelWeight i

lemma xiPickPoissonPrincipalMinorDet_eq_prod_indexWeight {kappa : Nat}
    (P : XiPickPoissonGram kappa) (I : Finset (Fin kappa)) :
    xiPickPoissonPrincipalMinorDet P I = I.prod (xiPickPoissonIndexWeight P) := by
  unfold xiPickPoissonPrincipalMinorDet xiPickPoissonDiagonalBlockDet xiPickPoissonKernelBlockDet
  rw [← Finset.prod_mul_distrib]
  simp [xiPickPoissonIndexWeight]

/-- Complementary index block inside `[κ]`. -/
def xiPickPoissonComplementIndices {kappa : Nat} (I : Finset (Fin kappa)) : Finset (Fin kappa) :=
  Finset.univ \ I

/-- In the abstract diagonal Pick--Poisson model, the inverse principal minor is the reciprocal
of the corresponding principal minor. -/
noncomputable def xiPickPoissonInversePrincipalMinorDet {kappa : Nat} (P : XiPickPoissonGram kappa)
    (I : Finset (Fin kappa)) : ℝ :=
  1 / xiPickPoissonPrincipalMinorDet P I

/-- The diagonal entry extracted from the inverse principal-minor package. -/
noncomputable def xiPickPoissonInverseDiagonalEntry {kappa : Nat} (P : XiPickPoissonGram kappa)
    (i : Fin kappa) : ℝ :=
  xiPickPoissonInversePrincipalMinorDet P ({i} : Finset (Fin kappa))

/-- The trace of the inverse principal-minor package. -/
noncomputable def xiPickPoissonInverseTrace {kappa : Nat} (P : XiPickPoissonGram kappa) : ℝ :=
  ∑ i : Fin kappa, xiPickPoissonInverseDiagonalEntry P i

lemma xiPickPoissonPrincipalMinorDet_ne_zero {kappa : Nat} (P : XiPickPoissonGram kappa)
    (hpoint : ∀ i, P.pointWeight i ≠ 0) (hkernel : ∀ i, P.kernelWeight i ≠ 0)
    (I : Finset (Fin kappa)) : xiPickPoissonPrincipalMinorDet P I ≠ 0 := by
  rw [xiPickPoissonPrincipalMinorDet_eq_prod_indexWeight]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => mul_ne_zero (hpoint i) (hkernel i)

lemma xiPickPoissonInversePrincipalMinorDet_eq_complement_ratio {kappa : Nat}
    (P : XiPickPoissonGram kappa)
    (hpoint : ∀ i, P.pointWeight i ≠ 0) (hkernel : ∀ i, P.kernelWeight i ≠ 0)
    (I : Finset (Fin kappa)) :
    xiPickPoissonInversePrincipalMinorDet P I =
      xiPickPoissonPrincipalMinorDet P (xiPickPoissonComplementIndices I) /
        xiPickPoissonPrincipalMinorDet P Finset.univ := by
  have hsubset : I ⊆ (Finset.univ : Finset (Fin kappa)) := by
    intro i hi
    simp
  have hsplit :
      xiPickPoissonPrincipalMinorDet P (xiPickPoissonComplementIndices I) *
          xiPickPoissonPrincipalMinorDet P I =
        xiPickPoissonPrincipalMinorDet P Finset.univ := by
    rw [xiPickPoissonPrincipalMinorDet_eq_prod_indexWeight,
      xiPickPoissonPrincipalMinorDet_eq_prod_indexWeight,
      xiPickPoissonPrincipalMinorDet_eq_prod_indexWeight, xiPickPoissonComplementIndices]
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (Finset.prod_sdiff (s₁ := I) (s₂ := (Finset.univ : Finset (Fin kappa)))
        (f := xiPickPoissonIndexWeight P) hsubset)
  have hI0 := xiPickPoissonPrincipalMinorDet_ne_zero P hpoint hkernel I
  have hU0 := xiPickPoissonPrincipalMinorDet_ne_zero P hpoint hkernel Finset.univ
  apply (eq_div_iff hU0).2
  rw [xiPickPoissonInversePrincipalMinorDet, ← hsplit]
  field_simp [hI0]

lemma xiPickPoissonInverseDiagonalEntry_eq_explicit {kappa : Nat} (P : XiPickPoissonGram kappa)
    (i : Fin kappa) :
    xiPickPoissonInverseDiagonalEntry P i = 1 / (P.pointWeight i * P.kernelWeight i) := by
  rw [xiPickPoissonInverseDiagonalEntry, xiPickPoissonInversePrincipalMinorDet]
  simp [xiPickPoissonPrincipalMinorDet, xiPickPoissonDiagonalBlockDet,
    xiPickPoissonKernelBlockDet]

lemma xiPickPoissonInverseTrace_eq_sum {kappa : Nat} (P : XiPickPoissonGram kappa) :
    xiPickPoissonInverseTrace P =
      ∑ i : Fin kappa, 1 / (P.pointWeight i * P.kernelWeight i) := by
  unfold xiPickPoissonInverseTrace
  refine Finset.sum_congr rfl ?_
  intro i hi
  simpa using xiPickPoissonInverseDiagonalEntry_eq_explicit P i

/-- Jacobi complement identity, singleton diagonal specialization, and the resulting trace
formula in the abstract Pick--Poisson product model. -/
def XiPickPoissonInversePrincipalMinorsJacobi {kappa : Nat} (P : XiPickPoissonGram kappa) : Prop :=
  (∀ i, P.pointWeight i ≠ 0) →
    (∀ i, P.kernelWeight i ≠ 0) →
      (∀ I, xiPickPoissonInversePrincipalMinorDet P I =
        xiPickPoissonPrincipalMinorDet P (xiPickPoissonComplementIndices I) /
          xiPickPoissonPrincipalMinorDet P Finset.univ) ∧
        (∀ i, xiPickPoissonInverseDiagonalEntry P i = 1 / (P.pointWeight i * P.kernelWeight i)) ∧
        xiPickPoissonInverseTrace P =
          ∑ i : Fin kappa, 1 / (P.pointWeight i * P.kernelWeight i)

/-- In the concrete Pick--Poisson product model, complement-index principal minors satisfy the
Jacobi ratio identity; specializing to singleton subsets gives the diagonal inverse formula, and
summing those diagonals yields the trace formula.
    prop:xi-pick-poisson-inverse-principal-minors-jacobi -/
theorem paper_xi_pick_poisson_inverse_principal_minors_jacobi {kappa : Nat}
    (P : XiPickPoissonGram kappa) : XiPickPoissonInversePrincipalMinorsJacobi P := by
  intro hpoint hkernel
  refine ⟨?_, ?_, xiPickPoissonInverseTrace_eq_sum P⟩
  · intro I
    exact xiPickPoissonInversePrincipalMinorDet_eq_complement_ratio P hpoint hkernel I
  · intro i
    exact xiPickPoissonInverseDiagonalEntry_eq_explicit P i

end Omega.Zeta
