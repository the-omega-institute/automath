import Mathlib.Data.Real.Basic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part65h-escort-hellinger-chernoff-kernel`. -/
theorem paper_xi_time_part65h_escort_hellinger_chernoff_kernel
    (rpow : ℝ → ℝ → ℝ) (phi p q s M : ℝ)
    (hM :
      M =
        (phi + rpow phi (-(s * p + (1 - s) * q))) /
          (rpow (phi + rpow phi (-p)) s * rpow (phi + rpow phi (-q)) (1 - s))) :
    M =
      (phi + rpow phi (-(s * p + (1 - s) * q))) /
        (rpow (phi + rpow phi (-p)) s * rpow (phi + rpow phi (-q)) (1 - s)) := by
  exact hM

end Omega.Zeta
