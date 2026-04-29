import Omega.Folding.DerivedFoldMultiplicityConvexOrderExtremal

namespace Omega.Folding

open scoped BigOperators

/-- For a balanced fold-multiplicity profile, the nontrivial Fourier energy remainder is exactly
`ρ (F - ρ)`. This is the quadratic-moment identity behind the collision floor.
    cor:derived-fold-multiplicity-fourier-collision-floor -/
theorem paper_derived_fold_multiplicity_fourier_collision_floor
    {F M : ℕ} (hF : 0 < F) (d : Fin F → ℕ)
    (hvals : ∀ i, d i = M / F ∨ d i = M / F + 1) (hsum : ∑ i, d i = M) :
    let ρ := M % F
    F * (∑ i, d i ^ 2) - M ^ 2 = ρ * (F - ρ) := by
  classical
  let a := M / F
  let ρ := M % F
  rcases paper_derived_fold_multiplicity_convex_order_extremal hF d hvals hsum with
    ⟨_, _, hsq⟩
  dsimp [ρ]
  have hMdecomp : M = F * a + ρ := by
    simpa [a, ρ, Nat.add_comm, Nat.mul_comm] using (Nat.mod_add_div M F).symm
  have hρle : ρ ≤ F := Nat.le_of_lt (Nat.mod_lt M hF)
  have hMoment :
      F * ((F - ρ) * a ^ 2 + ρ * (a + 1) ^ 2) = M ^ 2 + ρ * (F - ρ) := by
    have hMomentInt :
        (F * ((F - ρ) * a ^ 2 + ρ * (a + 1) ^ 2) : ℤ) = (M ^ 2 + ρ * (F - ρ) : ℤ) := by
      rw [hMdecomp]
      push_cast
      ring
    exact_mod_cast hMomentInt
  calc
    F * (∑ i, d i ^ 2) - M ^ 2 =
        F * ((F - ρ) * a ^ 2 + ρ * (a + 1) ^ 2) - M ^ 2 := by
          rw [hsq]
    _ = ρ * (F - ρ) := by
      rw [hMoment]
      exact Nat.add_sub_cancel_left (M ^ 2) (ρ * (F - ρ))

end Omega.Folding
