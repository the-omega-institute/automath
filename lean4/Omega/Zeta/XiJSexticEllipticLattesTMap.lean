import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Omega.Zeta.XiJDiscriminantMobiusRigidityCovariance

namespace Omega.Zeta

/-- The quartic-over-cubic Lattès map in the `t`-coordinate. -/
def xiJSexticLattesMap (t : ℚ) : ℚ :=
  (t ^ 4 + 6111488 * t ^ 2 + 2236612608 * t + 9487424438272) /
    (4 * (t - 1728) * xiJDiscriminantQuadratic t)

/-- The degree-`2` quotient coordinate fixed by the rational `2`-torsion involution. -/
def xiJSexticInvariantPi (t : ℚ) : ℚ :=
  (t - 1728) + 6365312 / (t - 1728)

/-- The resulting degree-`2` rational factor of the Lattès map. -/
def xiJSexticDegreeTwoQuotient (x : ℚ) : ℚ :=
  (x ^ 2 + 6912 * x + 11296768) / (4 * (x + 5318))

private lemma xiJSexticInvariantPi_den_ne_zero (t : ℚ) (ht : t ≠ 1728)
    (hQ : xiJDiscriminantQuadratic t ≠ 0) :
    xiJSexticInvariantPi t + 5318 ≠ 0 := by
  have hu : t - 1728 ≠ 0 := sub_ne_zero.mpr ht
  intro hzero
  have hmul := congrArg (fun z : ℚ => z * (t - 1728)) hzero
  unfold xiJSexticInvariantPi at hmul
  field_simp [hu] at hmul
  have hQ0 : t ^ 2 + 1862 * t + 161792 = 0 := by
    linarith
  exact hQ (by simpa [xiJDiscriminantQuadratic] using hQ0)

private lemma xiJSextic_factorization (t : ℚ) (ht : t ≠ 1728)
    (hQ : xiJDiscriminantQuadratic t ≠ 0) :
    xiJSexticLattesMap t = xiJSexticDegreeTwoQuotient (xiJSexticInvariantPi t) := by
  have hu : t - 1728 ≠ 0 := sub_ne_zero.mpr ht
  have hpiDen : xiJSexticInvariantPi t + 5318 ≠ 0 := xiJSexticInvariantPi_den_ne_zero t ht hQ
  unfold xiJSexticLattesMap xiJSexticDegreeTwoQuotient xiJSexticInvariantPi xiJDiscriminantQuadratic
  field_simp [hu, hQ, hpiDen]
  ring_nf

/-- For the quartic-over-cubic Lattès map attached to the discriminant elliptic curve
`y² = (t - 1728)(t² + 1862 t + 161792)`, the three finite branch values `1728, α, β` occur with
double quadratic fibers. -/
theorem paper_xi_j_sextic_elliptic_lattes_three_branch_square_factorization
    (t : ℝ) (ht : t ≠ 1728) (hQ : t ^ 2 + 1862 * t + 161792 ≠ 0) :
    let α : ℝ := -931 - 89 * Real.sqrt 89
    let β : ℝ := -931 + 89 * Real.sqrt 89
    let Q : ℝ := t ^ 2 + 1862 * t + 161792
    let L : ℝ := (t ^ 4 + 6111488 * t ^ 2 + 2236612608 * t + 9487424438272) / (4 * (t - 1728) * Q)
    L - 1728 = (t ^ 2 - 3456 * t - 3379328) ^ 2 / (4 * (t - 1728) * Q) ∧
      L - α =
        (t ^ 2 + (1862 + 178 * Real.sqrt 89) * t + 161792 - 307584 * Real.sqrt 89) ^ 2 /
          (4 * (t - 1728) * Q) ∧
      L - β =
        (t ^ 2 + (1862 - 178 * Real.sqrt 89) * t + 161792 + 307584 * Real.sqrt 89) ^ 2 /
          (4 * (t - 1728) * Q) := by
  have hsqrt89 : (Real.sqrt 89) ^ 2 = (89 : ℝ) := by
    rw [Real.sq_sqrt]
    positivity
  let N : ℝ := t ^ 4 + 6111488 * t ^ 2 + 2236612608 * t + 9487424438272
  let D : ℝ := 4 * (t - 1728) * (t ^ 2 + 1862 * t + 161792)
  have ht0 : t - 1728 ≠ 0 := sub_ne_zero.mpr ht
  have hD : D ≠ 0 := by
    have h4 : (4 : ℝ) ≠ 0 := by norm_num
    exact mul_ne_zero (mul_ne_zero h4 ht0) hQ
  have hQinv : t * (t + 1862) + 161792 ≠ 0 := by
    intro h0
    apply hQ
    nlinarith
  have hrewrite1728 : N / D - 1728 = (N - 1728 * D) / D := by
    dsimp [N, D]
    apply (mul_right_cancel₀ hQinv)
    field_simp [hD, hQinv]
  have hrewriteAlpha :
      N / D - (-931 - 89 * Real.sqrt 89) = (N - (-931 - 89 * Real.sqrt 89) * D) / D := by
    dsimp [N, D]
    apply (mul_right_cancel₀ hQinv)
    field_simp [hD, hQinv]
  have hrewriteBeta :
      N / D - (-931 + 89 * Real.sqrt 89) = (N - (-931 + 89 * Real.sqrt 89) * D) / D := by
    dsimp [N, D]
    apply (mul_right_cancel₀ hQinv)
    field_simp [hD, hQinv]
  have hnum1728 : N - 1728 * D = (t ^ 2 - 3456 * t - 3379328) ^ 2 := by
    dsimp [N, D]
    ring_nf
  have hnumAlpha :
      N - (-931 - 89 * Real.sqrt 89) * D =
        (t ^ 2 + (1862 + 178 * Real.sqrt 89) * t + 161792 - 307584 * Real.sqrt 89) ^ 2 := by
    dsimp [N, D]
    ring_nf
    repeat' rw [hsqrt89]
    ring_nf
  have hnumBeta :
      N - (-931 + 89 * Real.sqrt 89) * D =
        (t ^ 2 + (1862 - 178 * Real.sqrt 89) * t + 161792 + 307584 * Real.sqrt 89) ^ 2 := by
    dsimp [N, D]
    ring_nf
    repeat' rw [hsqrt89]
    ring_nf
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · rw [show
        (t ^ 4 + 6111488 * t ^ 2 + 2236612608 * t + 9487424438272) /
            (4 * (t - 1728) * (t ^ 2 + 1862 * t + 161792)) - 1728 =
          N / D - 1728 by rfl]
    rw [hrewrite1728, hnum1728]
  · rw [show
        (t ^ 4 + 6111488 * t ^ 2 + 2236612608 * t + 9487424438272) /
            (4 * (t - 1728) * (t ^ 2 + 1862 * t + 161792)) - (-931 - 89 * Real.sqrt 89) =
          N / D - (-931 - 89 * Real.sqrt 89) by rfl]
    rw [hrewriteAlpha, hnumAlpha]
  · rw [show
        (t ^ 4 + 6111488 * t ^ 2 + 2236612608 * t + 9487424438272) /
            (4 * (t - 1728) * (t ^ 2 + 1862 * t + 161792)) - (-931 + 89 * Real.sqrt 89) =
          N / D - (-931 + 89 * Real.sqrt 89) by rfl]
    rw [hrewriteBeta, hnumBeta]

/-- The rational `2`-torsion Möbius involution fixes the quotient coordinate `π`, and the sextic
Lattès map factors through the degree-`2` quotient `F`, hence becomes invariant under that
involution. This is the rational degree-drop package used in the paper-level argument.
    thm:xi-j-sextic-elliptic-lattes-degree-drop-by-2torsion -/
theorem paper_xi_j_sextic_elliptic_lattes_degree_drop_by_2torsion
    (t : ℚ) (ht : t ≠ 1728) (hQ : xiJDiscriminantQuadratic t ≠ 0) :
    xiJSexticInvariantPi (xiJTwoTorsionMobius t) = xiJSexticInvariantPi t ∧
      xiJSexticLattesMap t = xiJSexticDegreeTwoQuotient (xiJSexticInvariantPi t) ∧
      xiJSexticLattesMap (xiJTwoTorsionMobius t) = xiJSexticLattesMap t := by
  have hu : t - 1728 ≠ 0 := sub_ne_zero.mpr ht
  have hshift : xiJTwoTorsionMobius t - 1728 = 6365312 / (t - 1728) :=
    paper_xi_j_discriminant_mobius_rigidity_covariance.2.1 t
  have hpi :
      xiJSexticInvariantPi (xiJTwoTorsionMobius t) = xiJSexticInvariantPi t := by
    unfold xiJSexticInvariantPi
    rw [hshift]
    field_simp [hu]
    ring
  have hpiDen : xiJSexticInvariantPi t + 5318 ≠ 0 :=
    xiJSexticInvariantPi_den_ne_zero t ht hQ
  have hfactor : xiJSexticLattesMap t = xiJSexticDegreeTwoQuotient (xiJSexticInvariantPi t) :=
    xiJSextic_factorization t ht hQ
  have hphi_ne : xiJTwoTorsionMobius t ≠ 1728 := by
    intro hphi
    have hfrac : (6365312 : ℚ) / (t - 1728) = 0 := by
      simpa [hphi] using hshift.symm
    rcases (div_eq_zero_iff.mp hfrac) with hnum | hden
    · norm_num at hnum
    · exact hu hden
  have hQphi : xiJDiscriminantQuadratic (xiJTwoTorsionMobius t) ≠ 0 := by
    intro hphiQ
    have hcov := paper_xi_j_discriminant_mobius_rigidity_covariance.2.2 t ht
    rw [hphiQ] at hcov
    have hfrac : 6365312 * xiJDiscriminantQuadratic t / (t - 1728) ^ 2 = 0 := by
      simpa using hcov.symm
    rcases (div_eq_zero_iff.mp hfrac) with hnum | hden
    · rcases mul_eq_zero.mp hnum with hconst | hq
      · norm_num at hconst
      · exact hQ hq
    · exact hu (eq_zero_of_pow_eq_zero hden)
  have hfactorPhi :
      xiJSexticLattesMap (xiJTwoTorsionMobius t) =
        xiJSexticDegreeTwoQuotient (xiJSexticInvariantPi (xiJTwoTorsionMobius t)) :=
    xiJSextic_factorization (xiJTwoTorsionMobius t) hphi_ne hQphi
  refine ⟨hpi, hfactor, ?_⟩
  calc
    xiJSexticLattesMap (xiJTwoTorsionMobius t)
        = xiJSexticDegreeTwoQuotient (xiJSexticInvariantPi (xiJTwoTorsionMobius t)) := hfactorPhi
    _ = xiJSexticDegreeTwoQuotient (xiJSexticInvariantPi t) := by rw [hpi]
    _ = xiJSexticLattesMap t := hfactor.symm

end Omega.Zeta
