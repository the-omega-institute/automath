import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

/-- Paper label: `cor:pom-diagonal-rate-refresh-commute-effective-resistance`. -/
theorem paper_pom_diagonal_rate_refresh_commute_effective_resistance {X : Type*} [Fintype X]
    [DecidableEq X] (pi r : X → ℝ) (hit resistance : X → X → ℝ) (x y : X)
    (hpi : ∀ z, pi z ≠ 0) (hr : ∀ z, r z ≠ 0) (hxy : x ≠ y)
    (hHit : ∀ a b, a ≠ b → hit a b =
      1 / r a + (1 / pi b) * ∑ z : X, if z = b then 0 else pi z / r z)
    (hResistance : resistance x y =
      (∑ z : X, pi z / r z) * (1 / pi x + 1 / pi y)) :
    hit x y + hit y x = resistance x y := by
  classical
  let S : ℝ := ∑ z : X, pi z / r z
  have hsum (a : X) :
      (∑ z : X, if z = a then 0 else pi z / r z) = S - pi a / r a := by
    calc
      (∑ z : X, if z = a then 0 else pi z / r z)
          = Finset.sum (Finset.univ.erase a) (fun z : X => pi z / r z) := by
            rw [show Finset.univ.erase a = Finset.univ.filter (fun z : X => z ≠ a) by
              ext z
              simp]
            rw [Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro z hz
            by_cases hza : z = a
            · simp [hza]
            · simp [hza]
      _ = S - pi a / r a := by
        change Finset.sum (Finset.univ.erase a) (fun z : X => pi z / r z) =
          (∑ z : X, pi z / r z) - pi a / r a
        exact
          Finset.sum_erase_eq_sub (s := Finset.univ) (a := a)
            (f := fun z : X => pi z / r z) (Finset.mem_univ a)
  have hyx : y ≠ x := hxy.symm
  rw [hHit x y hxy, hHit y x hyx, hResistance, hsum x, hsum y]
  dsimp [S]
  field_simp [hpi x, hpi y, hr x, hr y]
  ring

end Omega.POM
