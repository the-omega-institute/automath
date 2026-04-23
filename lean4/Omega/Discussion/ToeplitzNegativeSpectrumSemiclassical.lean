import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Omega.Zeta.XiPickPoissonPrincipalMinorsPartition

open scoped BigOperators

namespace Omega.Discussion

/-- The negative-space asymptotic model obtained by negating the Pick--Poisson principal-minor
weights. -/
def discussion_toeplitz_negative_spectrum_semiclassical_negative_space_model {κ : ℕ}
    (P : Omega.Zeta.XiPickPoissonGram κ) : Finset (Fin κ) → ℝ :=
  fun I => -Omega.Zeta.xiPickPoissonPrincipalMinorDet P I

/-- The semiclassical trace proxy: sum the singleton negative-space minors. -/
def discussion_toeplitz_negative_spectrum_semiclassical_trace {κ : ℕ}
    (P : Omega.Zeta.XiPickPoissonGram κ) : ℝ :=
  ∑ i, Omega.Zeta.xiPickPoissonPrincipalMinorDet P ({i} : Finset (Fin κ))

/-- The semiclassical determinant proxy: the full Pick--Poisson principal minor. -/
def discussion_toeplitz_negative_spectrum_semiclassical_det {κ : ℕ}
    (P : Omega.Zeta.XiPickPoissonGram κ) : ℝ :=
  Omega.Zeta.xiPickPoissonPrincipalMinorDet P Finset.univ

/-- Package the Pick--Poisson Gram limit as the negative-space asymptotic model, then read the
trace and determinant from the existing principal-minor partition formula.
    prop:discussion-toeplitz-negative-spectrum-semiclassical -/
theorem paper_discussion_toeplitz_negative_spectrum_semiclassical {κ : ℕ}
    (P : Omega.Zeta.XiPickPoissonGram κ) :
    (discussion_toeplitz_negative_spectrum_semiclassical_negative_space_model P =
        fun I => -Omega.Zeta.xiPickPoissonPartitionWeight P I) ∧
      discussion_toeplitz_negative_spectrum_semiclassical_trace P =
        ∑ i, Omega.Zeta.xiPickPoissonPartitionWeight P ({i} : Finset (Fin κ)) ∧
      discussion_toeplitz_negative_spectrum_semiclassical_det P =
        Omega.Zeta.xiPickPoissonPartitionWeight P Finset.univ := by
  have hpartition := Omega.Zeta.paper_xi_pick_poisson_principal_minors_partition P
  refine ⟨?_, ?_, ?_⟩
  · funext I
    simp [discussion_toeplitz_negative_spectrum_semiclassical_negative_space_model, hpartition I]
  · unfold discussion_toeplitz_negative_spectrum_semiclassical_trace
    refine Finset.sum_congr rfl ?_
    intro i hi
    simpa using hpartition ({i} : Finset (Fin κ))
  · simpa [discussion_toeplitz_negative_spectrum_semiclassical_det] using hpartition Finset.univ

end Omega.Discussion
