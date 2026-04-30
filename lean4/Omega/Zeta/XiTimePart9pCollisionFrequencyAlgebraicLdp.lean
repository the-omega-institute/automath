import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9p-collision-frequency-algebraic-ldp`. -/
theorem paper_xi_time_part9p_collision_frequency_algebraic_ldp (rho u alpha : ℚ)
    (hu : u * (rho - 1) = rho * (rho ^ 2 - 2 * rho - 1))
    (ha :
      alpha * (2 * rho ^ 3 - 5 * rho ^ 2 + 4 * rho + 1) =
        (rho ^ 2 - 2 * rho - 1) * (rho - 1)) :
    (4 * u ^ 3 + 25 * u ^ 2 + 88 * u + 8) * (alpha ^ 3 - alpha ^ 2) +
      (u ^ 3 + 10 * u ^ 2 + 24 * u) * alpha - 2 * u ^ 2 = 0 := by
  have h1 : u * (rho - 1) - rho * (rho ^ 2 - 2 * rho - 1) = 0 := by
    linarith
  have h2 :
      alpha * (2 * rho ^ 3 - 5 * rho ^ 2 + 4 * rho + 1) -
        (rho ^ 2 - 2 * rho - 1) * (rho - 1) = 0 := by
    linarith
  let A : ℚ :=
    -580 * alpha ^ 3 * rho ^ 3 - 32 * alpha ^ 3 * rho ^ 2 * u ^ 2 -
      136 * alpha ^ 3 * rho ^ 2 * u + 1258 * alpha ^ 3 * rho ^ 2 +
      48 * alpha ^ 3 * rho * u ^ 2 + 300 * alpha ^ 3 * rho * u -
      648 * alpha ^ 3 * rho - 16 * alpha ^ 3 * u ^ 2 - 100 * alpha ^ 3 * u -
      754 * alpha ^ 3 + 8 * alpha ^ 2 * rho ^ 4 +
      16 * alpha ^ 2 * rho ^ 3 * u - 258 * alpha ^ 2 * rho ^ 3 +
      48 * alpha ^ 2 * rho ^ 2 * u ^ 2 + 100 * alpha ^ 2 * rho ^ 2 * u +
      626 * alpha ^ 2 * rho ^ 2 - 80 * alpha ^ 2 * rho * u ^ 2 -
      340 * alpha ^ 2 * rho * u - 1258 * alpha ^ 2 * rho +
      40 * alpha ^ 2 * u + 378 * alpha ^ 2 - 12 * alpha * rho ^ 4 -
      24 * alpha * rho ^ 3 * u + 322 * alpha * rho ^ 3 -
      24 * alpha * rho ^ 2 * u ^ 2 + 28 * alpha * rho ^ 2 * u -
      909 * alpha * rho ^ 2 + 44 * alpha * rho * u ^ 2 +
      88 * alpha * rho * u + 420 * alpha * rho + 12 * alpha * u ^ 2 -
      20 * alpha * u + 197 * alpha + 4 * rho ^ 4 + 8 * rho ^ 3 * u -
      25 * rho ^ 3 + 4 * rho ^ 2 * u ^ 2 - 24 * rho ^ 2 * u +
      43 * rho ^ 2 - 8 * rho * u ^ 2 - 9 * rho - 4 * u ^ 2 + 16 * u - 13
  let B : ℚ :=
    -290 * alpha ^ 2 * rho ^ 3 - 16 * alpha ^ 2 * rho ^ 2 * u ^ 2 -
      68 * alpha ^ 2 * rho ^ 2 * u + 484 * alpha ^ 2 * rho ^ 2 +
      16 * alpha ^ 2 * rho * u ^ 2 + 406 * alpha ^ 2 * rho * u +
      498 * alpha ^ 2 * rho + 16 * alpha ^ 2 * u ^ 3 +
      100 * alpha ^ 2 * u ^ 2 - 50 * alpha ^ 2 * u + 64 * alpha ^ 2 +
      4 * alpha * rho ^ 4 + 8 * alpha * rho ^ 3 * u -
      272 * alpha * rho ^ 3 + 16 * alpha * rho ^ 2 * u ^ 2 +
      16 * alpha * rho ^ 2 * u + 556 * alpha * rho ^ 2 -
      24 * alpha * rho * u ^ 2 + 184 * alpha * rho * u +
      184 * alpha * rho - 16 * alpha * u ^ 3 - 60 * alpha * u ^ 2 -
      376 * alpha * u - 4 * rho ^ 4 - 8 * rho ^ 3 * u + 21 * rho ^ 3 -
      4 * rho ^ 2 * u ^ 2 + 20 * rho ^ 2 * u - 22 * rho ^ 2 +
      12 * rho * u ^ 2 - rho * u - 13 * rho + 4 * u ^ 3 + 13 * u
  have hcert :
      8 *
          ((4 * u ^ 3 + 25 * u ^ 2 + 88 * u + 8) * (alpha ^ 3 - alpha ^ 2) +
            (u ^ 3 + 10 * u ^ 2 + 24 * u) * alpha - 2 * u ^ 2) =
        A * (u * (rho - 1) - rho * (rho ^ 2 - 2 * rho - 1)) +
          B *
            (alpha * (2 * rho ^ 3 - 5 * rho ^ 2 + 4 * rho + 1) -
              (rho ^ 2 - 2 * rho - 1) * (rho - 1)) := by
    dsimp only [A, B]
    ring_nf
  rw [h1, h2] at hcert
  norm_num at hcert
  simpa using hcert

end Omega.Zeta
