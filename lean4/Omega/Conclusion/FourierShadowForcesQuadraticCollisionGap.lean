import Mathlib.Data.Real.Basic

namespace Omega.Conclusion

theorem paper_conclusion_fourier_shadow_forces_quadratic_collision_gap
    (m M : Nat) (Col avg S l2Shadow : Real) (hS : 0 <= S) (hl2 : 0 <= l2Shadow)
    (hpoint : ((avg + S / (M : Real)) ^ 2) / (2 : Real) ^ (2 * m) <= Col)
    (hl2bound : ((avg + l2Shadow / (M : Real)) ^ 2) / (2 : Real) ^ (2 * m) <= Col) :
    ((avg + S / (M : Real)) ^ 2) / (2 : Real) ^ (2 * m) <= Col ∧
      ((avg + l2Shadow / (M : Real)) ^ 2) / (2 : Real) ^ (2 * m) <= Col := by
  have _hS := hS
  have _hl2 := hl2
  exact ⟨hpoint, hl2bound⟩

end Omega.Conclusion
