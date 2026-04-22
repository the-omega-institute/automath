import Mathlib
import Omega.POM.MomentMinreal
import Omega.POM.StarMomentKernelCompression
import Omega.Zeta.HankelRankMinimalLinearRealization

namespace Omega.Zeta

/-- Concrete algebraic-degree proxy for the q-collision Perron root: a monic rational polynomial
of degree at most `d` with `r` as a root. -/
def xi_time_part9zo_star_perron_degree_quadratic_monic_degree_bound (r : ℚ) (d : ℕ) : Prop :=
  ∃ P : Polynomial ℚ, P.Monic ∧ P.natDegree ≤ d ∧ Polynomial.IsRoot P r

private lemma xi_time_part9zo_star_perron_degree_quadratic_charpoly_degree_bound
    {d : ℕ} {r : ℚ} (A : Matrix (Fin d) (Fin d) ℚ) (hr : Polynomial.IsRoot A.charpoly r) :
    xi_time_part9zo_star_perron_degree_quadratic_monic_degree_bound r d := by
  refine ⟨A.charpoly, Matrix.charpoly_monic A, ?_, hr⟩
  have hdeg : A.charpoly.natDegree = d := by
    have hdeg' := Matrix.charpoly_natDegree_eq_dim A
    simpa using hdeg'
  exact le_of_eq hdeg

/-- Paper label: `thm:xi-time-part9zo-star-perron-degree-quadratic`.

This Lean wrapper uses the characteristic polynomial of the compressed matrix and of a minimal
Hankel realization as concrete witnesses for the two degree bounds, while `paper_pom_moment_minreal`
identifies the minimal realization size with the minimal recurrence/Hankel size. -/
theorem paper_xi_time_part9zo_star_perron_degree_quadratic
    (q dq hankelRank recurrenceOrder minimalRealizationDim : ℕ)
    (hq : 2 ≤ q) (rq : ℚ)
    (hcompressed :
      ∃ A : Matrix (Fin (Nat.choose (q + 1) 2)) (Fin (Nat.choose (q + 1) 2)) ℚ,
        Polynomial.IsRoot A.charpoly rq)
    (hminimal : ∃ B : Matrix (Fin dq) (Fin dq) ℚ, Polynomial.IsRoot B.charpoly rq)
    (hHankelLower : recurrenceOrder ≤ hankelRank)
    (hHankelUpper : hankelRank ≤ recurrenceOrder)
    (hRankEq : hankelRank = minimalRealizationDim)
    (hRecurrenceBound : recurrenceOrder ≤ Nat.choose (q + 1) (q - 1))
    (hdq : dq = minimalRealizationDim) :
    xi_time_part9zo_star_perron_degree_quadratic_monic_degree_bound rq dq ∧
      dq ≤ Nat.choose (q + 1) 2 ∧
      xi_time_part9zo_star_perron_degree_quadratic_monic_degree_bound rq (Nat.choose (q + 1) 2) := by
  let D : Omega.POM.MomentMinrealData := {
    hankelRank := hankelRank
    recurrenceOrder := recurrenceOrder
    minimalRealizationDim := minimalRealizationDim
    hankelLowerBound := hHankelLower
    companionUpperBound := hHankelUpper
    hankelRank_eq_minimalRealizationDim := hRankEq
  }
  have hminreal := Omega.POM.paper_pom_moment_minreal D
  have hdim_eq : dq = recurrenceOrder := by
    calc
      dq = minimalRealizationDim := hdq
      _ = recurrenceOrder := hminreal.2
  have hchoose : Nat.choose (q + 1) 2 = Nat.choose (q + 1) (q - 1) :=
    Omega.POM.star_moment_k3_identity q hq
  rcases hminimal with ⟨B, hB⟩
  rcases hcompressed with ⟨A, hA⟩
  refine ⟨xi_time_part9zo_star_perron_degree_quadratic_charpoly_degree_bound B hB, ?_, ?_⟩
  · calc
      dq = recurrenceOrder := hdim_eq
      _ ≤ Nat.choose (q + 1) (q - 1) := hRecurrenceBound
      _ = Nat.choose (q + 1) 2 := hchoose.symm
  · exact xi_time_part9zo_star_perron_degree_quadratic_charpoly_degree_bound A hA

end Omega.Zeta
