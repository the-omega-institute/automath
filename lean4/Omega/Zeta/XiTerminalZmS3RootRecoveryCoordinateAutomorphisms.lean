import Mathlib.Tactic

namespace Omega.Zeta

/-- The resolvent cubic from the xi-terminal `S₃` recovery theorem. -/
def xiTerminalZmResolventCubic (y z : ℚ) : ℚ :=
  z ^ 3 + (1 + 2 * y) * z ^ 2 - (1 + 4 * y + 4 * y ^ 2) * z - (1 + 5 * y + 13 * y ^ 2 + 8 * y ^ 3)

/-- The derivative of the resolvent cubic in the `z`-coordinate. -/
def xiTerminalZmResolventDerivative (y z : ℚ) : ℚ :=
  3 * z ^ 2 + 2 * (1 + 2 * y) * z - (1 + 4 * y + 4 * y ^ 2)

/-- The `+` branch in the companion-root recovery formula. -/
def xiTerminalZmRecoverPlus (y z w : ℚ) : ℚ :=
  -((1 + 2 * y) + z) / 2 + w / (2 * xiTerminalZmResolventDerivative y z)

/-- The `-` branch in the companion-root recovery formula. -/
def xiTerminalZmRecoverMinus (y z w : ℚ) : ℚ :=
  -((1 + 2 * y) + z) / 2 - w / (2 * xiTerminalZmResolventDerivative y z)

/-- The three-cycle on the ordered root set `(z₁,z₂,z₃)`. -/
def xiTerminalZmSigmaPerm : Equiv.Perm (Fin 3) where
  toFun
    | 0 => 1
    | 1 => 2
    | 2 => 0
  invFun
    | 0 => 2
    | 1 => 0
    | 2 => 1
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

/-- The transposition exchanging the companion roots `z₂` and `z₃`. -/
def xiTerminalZmIotaPerm : Equiv.Perm (Fin 3) where
  toFun
    | 0 => 0
    | 1 => 2
    | 2 => 1
  invFun
    | 0 => 0
    | 1 => 2
    | 2 => 1
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

/-- A concrete nonabelian-generation witness for the coordinate permutations. -/
def xiTerminalZmGeneratesS3 : Prop :=
  xiTerminalZmSigmaPerm ≠ 1 ∧
    xiTerminalZmIotaPerm ≠ 1 ∧
    xiTerminalZmSigmaPerm ^ 2 ≠ 1 ∧
    xiTerminalZmIotaPerm * xiTerminalZmSigmaPerm ≠ xiTerminalZmSigmaPerm * xiTerminalZmIotaPerm

private lemma xiTerminalZm_sigma_cube :
    xiTerminalZmSigmaPerm ^ 3 = 1 := by
  ext i
  fin_cases i <;> rfl

private lemma xiTerminalZm_iota_square :
    xiTerminalZmIotaPerm ^ 2 = 1 := by
  ext i
  fin_cases i <;> rfl

private lemma xiTerminalZm_iota_sigma_square :
    (xiTerminalZmIotaPerm * xiTerminalZmSigmaPerm) ^ 2 = 1 := by
  ext i
  fin_cases i <;> rfl

private lemma xiTerminalZm_generatesS3 :
    xiTerminalZmGeneratesS3 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have h0 := congrArg (fun τ : Equiv.Perm (Fin 3) => τ 0) h
    have hneq : (1 : Fin 3) ≠ 0 := by decide
    exact hneq (by simpa [xiTerminalZmSigmaPerm] using h0)
  · intro h
    have h1 := congrArg (fun τ : Equiv.Perm (Fin 3) => τ 1) h
    have hneq : (2 : Fin 3) ≠ 1 := by decide
    exact hneq (by simpa [xiTerminalZmIotaPerm] using h1)
  · intro h
    have h0 := congrArg (fun τ : Equiv.Perm (Fin 3) => τ 0) h
    have hneq : (2 : Fin 3) ≠ 0 := by decide
    exact hneq (by simpa [pow_two, xiTerminalZmSigmaPerm] using h0)
  · intro h
    have h0 := congrArg (fun τ : Equiv.Perm (Fin 3) => τ 0) h
    have hneq : (2 : Fin 3) ≠ 1 := by decide
    exact hneq (by simpa [xiTerminalZmIotaPerm, xiTerminalZmSigmaPerm] using h0)

/-- The companion roots are recovered from their sum and difference, and the induced coordinate
permutations satisfy the `S₃` relations on the ordered root triple.
    thm:xi-terminal-zm-s3-root-recovery-coordinate-automorphisms -/
theorem paper_xi_terminal_zm_s3_root_recovery_coordinate_automorphisms
    (y z₁ z₂ z₃ w : ℚ)
    (hzsum : z₂ + z₃ = -((1 + 2 * y) + z₁))
    (hderiv : xiTerminalZmResolventDerivative y z₁ ≠ 0)
    (hzdiff : z₂ - z₃ = w / xiTerminalZmResolventDerivative y z₁) :
    (xiTerminalZmRecoverPlus y z₁ w = z₂ ∧ xiTerminalZmRecoverMinus y z₁ w = z₃) ∧
      xiTerminalZmSigmaPerm ^ 3 = 1 ∧
      xiTerminalZmIotaPerm ^ 2 = 1 ∧
      (xiTerminalZmIotaPerm * xiTerminalZmSigmaPerm) ^ 2 = 1 ∧
      xiTerminalZmGeneratesS3 := by
  let D := xiTerminalZmResolventDerivative y z₁
  have hz₂ :
      xiTerminalZmRecoverPlus y z₁ w = z₂ := by
    have htwo : (2 : ℚ) ≠ 0 := by norm_num
    have hrecover :
        2 * xiTerminalZmRecoverPlus y z₁ w = -((1 + 2 * y) + z₁) + w / D := by
      unfold xiTerminalZmRecoverPlus D
      field_simp [hderiv]
    have hz₂_twice : 2 * z₂ = -((1 + 2 * y) + z₁) + w / D := by
      unfold D
      linarith [hzsum, hzdiff]
    apply (mul_right_inj' htwo).mp
    have hEq : 2 * xiTerminalZmRecoverPlus y z₁ w = 2 * z₂ := by
      calc
        2 * xiTerminalZmRecoverPlus y z₁ w = -((1 + 2 * y) + z₁) + w / D := hrecover
        _ = 2 * z₂ := hz₂_twice.symm
    simpa [mul_comm] using hEq
  have hz₃ :
      xiTerminalZmRecoverMinus y z₁ w = z₃ := by
    have htwo : (2 : ℚ) ≠ 0 := by norm_num
    have hrecover :
        2 * xiTerminalZmRecoverMinus y z₁ w = -((1 + 2 * y) + z₁) - w / D := by
      unfold xiTerminalZmRecoverMinus D
      field_simp [hderiv]
    have hz₃_twice : 2 * z₃ = -((1 + 2 * y) + z₁) - w / D := by
      unfold D
      linarith [hzsum, hzdiff]
    apply (mul_right_inj' htwo).mp
    have hEq : 2 * xiTerminalZmRecoverMinus y z₁ w = 2 * z₃ := by
      calc
        2 * xiTerminalZmRecoverMinus y z₁ w = -((1 + 2 * y) + z₁) - w / D := hrecover
        _ = 2 * z₃ := hz₃_twice.symm
    simpa [mul_comm] using hEq
  exact ⟨⟨hz₂, hz₃⟩, xiTerminalZm_sigma_cube, xiTerminalZm_iota_square,
    xiTerminalZm_iota_sigma_square, xiTerminalZm_generatesS3⟩

end Omega.Zeta
