import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-leyang-eta-theta-norm-cubic-collapse`. -/
theorem paper_conclusion_leyang_eta_theta_norm_cubic_collapse (eta v : Int)
    (hv :
      v ^ 2 = 2304 * eta ^ 4 - 8896 * eta ^ 3 + 13157 * eta ^ 2 - 8896 * eta +
        2304) :
    (let Q4 : Int := 512 * eta ^ 4 - 2240 * eta ^ 3 + 3465 * eta ^ 2 - 2240 * eta +
        512
      let B : Int := 128 * eta ^ 2 - 265 * eta + 128
      (3 * Q4 + 32 * (eta - 1) ^ 2 * v) * (3 * Q4 - 32 * (eta - 1) ^ 2 * v) =
        -eta * B ^ 3) := by
  dsimp only
  calc
    (3 * (512 * eta ^ 4 - 2240 * eta ^ 3 + 3465 * eta ^ 2 - 2240 * eta + 512) +
            32 * (eta - 1) ^ 2 * v) *
        (3 * (512 * eta ^ 4 - 2240 * eta ^ 3 + 3465 * eta ^ 2 - 2240 * eta + 512) -
            32 * (eta - 1) ^ 2 * v) =
        9 * (512 * eta ^ 4 - 2240 * eta ^ 3 + 3465 * eta ^ 2 - 2240 * eta + 512) ^ 2 -
          (32 * (eta - 1) ^ 2) ^ 2 * v ^ 2 := by
      ring
    _ = -eta * (128 * eta ^ 2 - 265 * eta + 128) ^ 3 := by
      rw [hv]
      ring

end Omega.Conclusion
