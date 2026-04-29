import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9gb-zg-address-fractal-dimension`. -/
theorem paper_xi_time_part9gb_zg_address_fractal_dimension
    (allowedCylinderCount F : ℕ → ℕ) (hF0 : F 0 = 0) (hF1 : F 1 = 1)
    (hFstep : ∀ n, F (n + 2) = F (n + 1) + F n)
    (hC0 : allowedCylinderCount 0 = 1) (hC1 : allowedCylinderCount 1 = 2)
    (hCstep : ∀ n,
      allowedCylinderCount (n + 2) = allowedCylinderCount (n + 1) + allowedCylinderCount n) :
    ∀ n, allowedCylinderCount n = F (n + 2) := by
  refine Nat.twoStepInduction ?_ ?_ ?_
  · rw [hC0, hFstep 0, hF1, hF0]
  · rw [hC1, hFstep 1, hFstep 0, hF1, hF0]
  · intro n hn hn1
    calc
      allowedCylinderCount (n + 2) =
          allowedCylinderCount (n + 1) + allowedCylinderCount n := hCstep n
      _ = F ((n + 1) + 2) + F (n + 2) := by rw [hn1, hn]
      _ = F ((n + 2) + 2) := by rw [hFstep (n + 2)]

end Omega.Zeta
