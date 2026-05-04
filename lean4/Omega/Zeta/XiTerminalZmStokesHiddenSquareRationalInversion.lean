import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-terminal-zm-stokes-hidden-square-rational-inversion`. -/
theorem paper_xi_terminal_zm_stokes_hidden_square_rational_inversion {K : Type*}
    [Field K] [CharZero K] (t : K)
    (ht : 162 * t ^ 3 + 1593 * t ^ 2 + 1998 * t + 1184 = 0) :
    (let s : K := (-71045 - 13947 * t + 12258 * t ^ 2) / 1199;
      s ^ 2 = 10080 * t ^ 2 + 16224 * t + 12761) ∧
      (let y1 : K := (36774 * t ^ 2 - 329601 * t - 269488) /
          (9592 * (69 * t + 110));
        (276 * t + 440) * y1 ^ 2 + (240 * t + 47) * y1 - (30 * t + 64) = 0) ∧
      (let y2 : K := (-36774 * t ^ 2 - 245919 * t + 156782) /
          (9592 * (69 * t + 110));
        (276 * t + 440) * y2 ^ 2 + (240 * t + 47) * y2 - (30 * t + 64) = 0) := by
  have h1199 : (1199 : K) ≠ 0 := by norm_num
  have h9592 : (9592 : K) ≠ 0 := by norm_num
  have h69t110 : (69 * t + 110 : K) ≠ 0 := by
    intro h
    have hconst : (16924288 : K) = 0 := by
      linear_combination
        (12167 : K) * ht -
          (27 * (1058 * t ^ 2 + 8717 * t - 848) : K) * h
    norm_num at hconst
  have hden : (9592 * (69 * t + 110) : K) ≠ 0 := by
    exact mul_ne_zero h9592 h69t110
  have hquad : (12100 + t * 15180 + t ^ 2 * 4761 : K) ≠ 0 := by
    have hsquare : (12100 + t * 15180 + t ^ 2 * 4761 : K) = (69 * t + 110) ^ 2 := by
      ring
    rw [hsquare]
    exact pow_ne_zero 2 h69t110
  constructor
  · dsimp
    field_simp [h1199]
    linear_combination (927522 * t - 11231279 : K) * ht
  constructor
  · let N : K := 36774 * t ^ 2 - 329601 * t - 269488
    let D : K := 9592 * (69 * t + 110)
    have hD : D ≠ 0 := by simpa [D] using hden
    have hnum :
        (276 * t + 440) * N ^ 2 + (240 * t + 47) * N * D -
            (30 * t + 64) * D ^ 2 = 0 := by
      dsimp [N, D]
      linear_combination
        (2303964648 * t ^ 2 - 24225509916 * t - 44475864840 : K) * ht
    change
      (276 * t + 440) * (N / D) ^ 2 + (240 * t + 47) * (N / D) -
          (30 * t + 64) = 0
    calc
      (276 * t + 440) * (N / D) ^ 2 + (240 * t + 47) * (N / D) -
          (30 * t + 64) =
          ((276 * t + 440) * N ^ 2 + (240 * t + 47) * N * D -
            (30 * t + 64) * D ^ 2) / D ^ 2 := by
            field_simp [hD]
      _ = 0 := by simp [hnum]
  · let N : K := -36774 * t ^ 2 - 245919 * t + 156782
    let D : K := 9592 * (69 * t + 110)
    have hD : D ≠ 0 := by simpa [D] using hden
    have hnum :
        (276 * t + 440) * N ^ 2 + (240 * t + 47) * N * D -
            (30 * t + 64) * D ^ 2 = 0 := by
      dsimp [N, D]
      linear_combination
        (2303964648 * t ^ 2 - 24225509916 * t - 44475864840 : K) * ht
    change
      (276 * t + 440) * (N / D) ^ 2 + (240 * t + 47) * (N / D) -
          (30 * t + 64) = 0
    calc
      (276 * t + 440) * (N / D) ^ 2 + (240 * t + 47) * (N / D) -
          (30 * t + 64) =
          ((276 * t + 440) * N ^ 2 + (240 * t + 47) * N * D -
            (30 * t + 64) * D ^ 2) / D ^ 2 := by
            field_simp [hD]
      _ = 0 := by simp [hnum]

end Omega.Zeta
