import Omega.Zeta.AbelDepolarizationRootUnityRotation
import Omega.Zeta.AbelMobiusLinearization

namespace Omega.Conclusion

open scoped BigOperators

noncomputable section

/-- The cyclotomic coordinate used by depolarization. -/
def conclusion_xi_depolarization_mobius_orthogonality_cyclotomicMode
    (m : ℕ) (u : ℂ) : ℂ × ℂ :=
  (Omega.Zeta.abel_depolarization_root_unity_rotation_geometric_sum m u, 0)

/-- The primitive geometric-layer coordinate isolated by Möbius linearization. -/
def conclusion_xi_depolarization_mobius_orthogonality_mobiusMode
    (E : ℕ → ℂ) : ℂ × ℂ :=
  (0, Omega.Zeta.abel_mobius_linearization_linear_expression E)

/-- Coordinate pairing separating cyclotomic and primitive geometric axes. -/
def conclusion_xi_depolarization_mobius_orthogonality_pairing
    (x y : ℂ × ℂ) : ℂ :=
  x.1 * y.1 + x.2 * y.2

/-- The depolarization package supplied by the root-of-unity rotation theorem. -/
def conclusion_xi_depolarization_mobius_orthogonality_depolarizationPackage
    (psi h : ℕ → ℕ) (b m rho delta : ℕ) : Prop :=
  Omega.Zeta.xiAbelCoeff psi (b ^ m) =
      Omega.Zeta.xiAbelDecimation m (Omega.Zeta.xiAbelCoeff psi b) ∧
    Omega.Zeta.xiAbelDampedSeries psi (b ^ m) delta =
      Omega.Zeta.xiAbelDecimation m (Omega.Zeta.xiAbelDampedSeries psi b delta) ∧
    Omega.Zeta.xiAbelAnalyticRemainder h (b ^ m) delta =
      Omega.Zeta.xiAbelDecimation m (Omega.Zeta.xiAbelAnalyticRemainder h b delta) ∧
    Omega.Zeta.xiAbelPoleMap (b ^ m) rho delta =
      (Omega.Zeta.xiAbelPoleMap b rho delta) ^ m ∧
    (∀ u : ℂ,
      1 - u ^ m =
        (1 - u) * Omega.Zeta.abel_depolarization_root_unity_rotation_geometric_sum m u) ∧
    (∀ {u : ℂ}, u ≠ 1 →
      (Omega.Zeta.abel_depolarization_root_unity_rotation_geometric_sum m u = 0 ↔
        u ^ m = 1)) ∧
    Omega.Zeta.abel_depolarization_root_unity_rotation_regularized_kernel m 1 =
      -((m - 1 : ℂ) / 2)

/-- The Möbius linearization package after neutralizing all higher geometric tails. -/
def conclusion_xi_depolarization_mobius_orthogonality_mobiusPackage
    (E mu h : ℕ → ℂ) (k : ℕ) (R M : ℝ) : Prop :=
  (∀ n : ℕ,
      Omega.Zeta.abel_mobius_linearization_multiscale E mu n =
        Omega.Zeta.abel_mobius_linearization_zero_tail E n) ∧
    Omega.Zeta.abel_mobius_linearization_zero_tail E 1 =
      Omega.Zeta.abel_mobius_linearization_linear_expression E ∧
    ∀ r : ℂ, ‖r‖ ≤ 1 →
      ‖(tsum fun n : ℕ => h (k * n) * r ^ n) - h 0‖ ≤
        M * (1 / R) ^ k / (1 - (1 / R) ^ k)

/-- The two axes are orthogonal in the direct-product coordinate pairing. -/
def conclusion_xi_depolarization_mobius_orthogonality_axisOrthogonal
    (m : ℕ) (E : ℕ → ℂ) : Prop :=
  ∀ u : ℂ,
    conclusion_xi_depolarization_mobius_orthogonality_pairing
      (conclusion_xi_depolarization_mobius_orthogonality_cyclotomicMode m u)
      (conclusion_xi_depolarization_mobius_orthogonality_mobiusMode E) = 0

/-- Paper label: `thm:conclusion-xi-depolarization-mobius-orthogonality`. -/
theorem paper_conclusion_xi_depolarization_mobius_orthogonality
    (psi arithRemainder : ℕ → ℕ) (b m rho delta : ℕ)
    (E mu analyticTail : ℕ → ℂ) (k : ℕ) (R M : ℝ)
    (hmu : ∀ n : ℕ, n.divisors.sum mu = if n = 1 then 1 else 0)
    (hk : 0 < k) (hR : 1 < R) (hM : 0 ≤ M)
    (hbound : ∀ n : ℕ, ‖analyticTail n‖ ≤ M * (1 / R) ^ n) :
    conclusion_xi_depolarization_mobius_orthogonality_depolarizationPackage
        psi arithRemainder b m rho delta ∧
      conclusion_xi_depolarization_mobius_orthogonality_mobiusPackage
        E mu analyticTail k R M ∧
      conclusion_xi_depolarization_mobius_orthogonality_axisOrthogonal m E := by
  refine ⟨?_, ?_, ?_⟩
  · exact Omega.Zeta.paper_abel_depolarization_root_unity_rotation
      psi arithRemainder b m rho delta
  · exact Omega.Zeta.paper_abel_mobius_linearization
      E mu analyticTail k R M hmu hk hR hM hbound
  · intro u
    simp [conclusion_xi_depolarization_mobius_orthogonality_pairing,
      conclusion_xi_depolarization_mobius_orthogonality_cyclotomicMode,
      conclusion_xi_depolarization_mobius_orthogonality_mobiusMode]

end

end Omega.Conclusion
