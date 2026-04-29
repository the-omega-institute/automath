import Mathlib.Tactic
import Omega.Conclusion.LeyangRho456AtomicWallIdentities
import Omega.Conclusion.LeyangRho45AffineCoordinateSystemOnS5Simplex

namespace Omega.Conclusion

/-- Affine recovery certificate for the `ρ₆` atom from the `ρ₅` atom and the fourth wall. -/
def conclusion_leyang_rho456_two_channel_completeness_rho6AffineRecovery
    {M : Type*} [AddCommGroup M] (mu5 mu6 sigma4 : M) : Prop :=
  24 • mu6 - 20 • mu5 = sigma4

/-- The `ρ₄/ρ₅` channel pair is injective on normalized `S₅` density vectors. -/
def conclusion_leyang_rho456_two_channel_completeness_rho45Injective : Prop :=
  ∀ v w : LeyangS5DensityVector,
    IsNormalizedDensity v →
      IsNormalizedDensity w →
        rho4Coordinate v = rho4Coordinate w →
          rho5Coordinates v = rho5Coordinates w →
            v = w

/-- Paper-facing two-channel completeness and `ρ₆` redundancy statement. -/
def conclusion_leyang_rho456_two_channel_completeness_statement : Prop :=
  (∀ {M : Type*} [AddCommGroup M] (mu4 mu5 mu6 sigma4 sigma6 : M),
      24 • mu6 - 20 • mu5 = sigma4 →
        24 • mu4 - 30 • mu5 = -sigma6 →
          conclusion_leyang_rho456_two_channel_completeness_rho6AffineRecovery
            mu5 mu6 sigma4) ∧
    conclusion_leyang_rho456_two_channel_completeness_rho45Injective ∧
      ∀ v : LeyangS5DensityVector,
        IsNormalizedDensity v → recoveredDensityVector (twoChannelCoordinates v) = v

/-- Paper label: `thm:conclusion-leyang-rho456-two-channel-completeness`. -/
theorem paper_conclusion_leyang_rho456_two_channel_completeness :
    conclusion_leyang_rho456_two_channel_completeness_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro M _ mu4 mu5 mu6 sigma4 sigma6 h46 h45
    exact (paper_conclusion_leyang_rho456_atomic_wall_identities
      (mu4 := mu4) (mu5 := mu5) (mu6 := mu6) (sigma4 := sigma4) (sigma6 := sigma6)
      h46 h45).1
  · intro v w hv hw h4 h5
    have hx1 : v 6 / 5 = w 6 / 5 := congrArg Prod.fst h5
    have h5_tail1 : (v 5 / 5, v 4 / 5, (2 * v 3 + v 4) / 5,
        (2 * (v 1 + v 2 + v 5)) / 5) =
        (w 5 / 5, w 4 / 5, (2 * w 3 + w 4) / 5,
          (2 * (w 1 + w 2 + w 5)) / 5) := congrArg Prod.snd h5
    have hx2 : v 5 / 5 = w 5 / 5 := congrArg Prod.fst h5_tail1
    have h5_tail2 : (v 4 / 5, (2 * v 3 + v 4) / 5,
        (2 * (v 1 + v 2 + v 5)) / 5) =
        (w 4 / 5, (2 * w 3 + w 4) / 5,
          (2 * (w 1 + w 2 + w 5)) / 5) := congrArg Prod.snd h5_tail1
    have hx3 : v 4 / 5 = w 4 / 5 := congrArg Prod.fst h5_tail2
    have h5_tail3 : ((2 * v 3 + v 4) / 5, (2 * (v 1 + v 2 + v 5)) / 5) =
        ((2 * w 3 + w 4) / 5, (2 * (w 1 + w 2 + w 5)) / 5) :=
      congrArg Prod.snd h5_tail2
    have hx4 : (2 * v 3 + v 4) / 5 = (2 * w 3 + w 4) / 5 :=
      congrArg Prod.fst h5_tail3
    have hx5 : (2 * (v 1 + v 2 + v 5)) / 5 =
        (2 * (w 1 + w 2 + w 5)) / 5 := congrArg Prod.snd h5_tail3
    have hx6 : (v 1 + 2 * v 2 + v 4 + v 5) / 4 =
        (w 1 + 2 * w 2 + w 4 + w 5) / 4 := by
      simpa [rho4Coordinate] using h4
    exact paper_conclusion_leyang_rho45_affine_coordinate_system_on_s5_simplex.2 v w hv hw
      (by
        change
          ({ x1 := v 6 / 5, x2 := v 5 / 5, x3 := v 4 / 5,
              x4 := (2 * v 3 + v 4) / 5,
              x5 := (2 * (v 1 + v 2 + v 5)) / 5,
              x6 := (v 1 + 2 * v 2 + v 4 + v 5) / 4 } : LeyangTwoChannelCoordinates) =
            { x1 := w 6 / 5, x2 := w 5 / 5, x3 := w 4 / 5,
              x4 := (2 * w 3 + w 4) / 5,
              x5 := (2 * (w 1 + w 2 + w 5)) / 5,
              x6 := (w 1 + 2 * w 2 + w 4 + w 5) / 4 }
        rw [hx1, hx2, hx3, hx4, hx5, hx6])
  · exact paper_conclusion_leyang_rho45_affine_coordinate_system_on_s5_simplex.1

end Omega.Conclusion
