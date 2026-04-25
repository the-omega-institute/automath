import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-real-input40-cinf-quartic-elimination`. -/
theorem paper_xi_real_input40_cinf_quartic_elimination {b C : Rat}
    (hb : b ^ 4 + b ^ 3 - 9 * b ^ 2 + 6 * b - 1 = 0)
    (hC : 2 * C * b * (1 - b) * (6 - 18 * b + 3 * b ^ 2 + 4 * b ^ 3) = 1) :
    88864 * C ^ 4 - 22216 * C ^ 3 - 275864 * C ^ 2 - 3646 * C + 1 = 0 := by
  have hCpoly :
      2 * C * b * (1 - b) * (6 - 18 * b + 3 * b ^ 2 + 4 * b ^ 3) - 1 = 0 := by
    nlinarith
  have hcert :
      88864 * C ^ 4 - 22216 * C ^ 3 - 275864 * C ^ 2 - 3646 * C + 1 =
        (1969728 * C ^ 4 * b ^ 4 + 224048 * C ^ 4 * b ^ 3 -
            10245312 * C ^ 4 * b ^ 2 + 8095968 * C ^ 4 * b - 88864 * C ^ 4 -
            83040 * C ^ 3 * b ^ 4 - 321928 * C ^ 3 * b ^ 3 +
            280352 * C ^ 3 * b ^ 2 + 1228072 * C ^ 3 * b - 696880 * C ^ 3 +
            320 * C ^ 2 * b ^ 4 - 1120 * C ^ 2 * b ^ 3 + 2948 * C ^ 2 * b ^ 2 +
            19728 * C ^ 2 * b - 580 * C ^ 2 - 8 * C * b + 10 * C) *
          (b ^ 4 + b ^ 3 - 9 * b ^ 2 + 6 * b - 1) +
        (246216 * C ^ 3 * b ^ 3 + 335776 * C ^ 3 * b ^ 2 -
            2092024 * C ^ 3 * b + 719096 * C ^ 3 - 10380 * C ^ 2 * b ^ 3 -
            53216 * C ^ 2 * b ^ 2 + 20424 * C ^ 2 * b + 276444 * C ^ 2 +
            40 * C * b ^ 3 - 90 * C * b ^ 2 + 56 * C * b + 3636 * C - 1) *
          (2 * C * b * (1 - b) * (6 - 18 * b + 3 * b ^ 2 + 4 * b ^ 3) - 1) := by
    ring
  rw [hcert, hb, hCpoly]
  ring

end Omega.Zeta
