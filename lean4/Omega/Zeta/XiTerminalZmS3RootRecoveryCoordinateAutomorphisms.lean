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

/-- Labels for the three roots of the cubic resolvent. -/
inductive XiTerminalZmS3RootIndex
  | one
  | two
  | three
  deriving DecidableEq, Repr

/-- The displayed ordering of the three roots. -/
def xiTerminalZmS3RootValue (z1 z2 z3 : ℚ) : XiTerminalZmS3RootIndex → ℚ
  | .one => z1
  | .two => z2
  | .three => z3

/-- The 3-cycle acting on the ordered roots. -/
def xiTerminalZmS3SigmaIndex : XiTerminalZmS3RootIndex → XiTerminalZmS3RootIndex
  | .one => .two
  | .two => .three
  | .three => .one

/-- The involution swapping the two conjugate branches. -/
def xiTerminalZmS3IotaIndex : XiTerminalZmS3RootIndex → XiTerminalZmS3RootIndex
  | .one => .one
  | .two => .three
  | .three => .two

/-- The coordinate formula for the `σ`-image of the distinguished root. -/
def xiTerminalZmS3SigmaCoordinate (y z w dRdz : ℚ) : ℚ :=
  -((1 + 2 * y) + z) / 2 + w / (2 * dRdz)

/-- The coordinate formula for the conjugate branch. -/
def xiTerminalZmS3IotaCoordinate (y z w dRdz : ℚ) : ℚ :=
  -((1 + 2 * y) + z) / 2 - w / (2 * dRdz)

/-- `σ` cycles the three ordered roots. -/
def xiTerminalZmS3SigmaPermutesRoots (z1 z2 z3 : ℚ) : Prop :=
  xiTerminalZmS3RootValue z1 z2 z3 (xiTerminalZmS3SigmaIndex .one) = z2 ∧
    xiTerminalZmS3RootValue z1 z2 z3 (xiTerminalZmS3SigmaIndex .two) = z3 ∧
    xiTerminalZmS3RootValue z1 z2 z3 (xiTerminalZmS3SigmaIndex .three) = z1

/-- `ι` swaps the two conjugate roots. -/
def xiTerminalZmS3IotaSwapsConjugates (z1 z2 z3 : ℚ) : Prop :=
  xiTerminalZmS3RootValue z1 z2 z3 (xiTerminalZmS3IotaIndex .two) = z3 ∧
    xiTerminalZmS3RootValue z1 z2 z3 (xiTerminalZmS3IotaIndex .three) = z2

/-- The index maps satisfy the standard `S₃` relations. -/
def xiTerminalZmS3GeneratesS3 : Prop :=
  (∀ i, xiTerminalZmS3SigmaIndex (xiTerminalZmS3SigmaIndex (xiTerminalZmS3SigmaIndex i)) = i) ∧
    (∀ i, xiTerminalZmS3IotaIndex (xiTerminalZmS3IotaIndex i) = i) ∧
    (∀ i,
      xiTerminalZmS3IotaIndex
          (xiTerminalZmS3SigmaIndex
            (xiTerminalZmS3IotaIndex (xiTerminalZmS3SigmaIndex i))) = i)

lemma xi_terminal_zm_s3_generates_s3 : xiTerminalZmS3GeneratesS3 := by
  refine ⟨?_, ?_, ?_⟩ <;> intro i <;> cases i <;> rfl

/-- Indexed companion to the paper theorem above: the same root-recovery formulas packaged through
explicit root labels and index-level `S₃` relations. -/
theorem paper_xi_terminal_zm_s3_root_recovery_coordinate_automorphisms_indexed
    {y z1 z2 z3 w dRdz : ℚ} (hdRdz : dRdz ≠ 0)
    (hsum : z2 + z3 = -((1 + 2 * y) + z1)) (hdiff : z2 - z3 = w / dRdz) :
    z2 = -((1 + 2 * y) + z1) / 2 + w / (2 * dRdz) ∧
      z3 = -((1 + 2 * y) + z1) / 2 - w / (2 * dRdz) ∧
      xiTerminalZmS3SigmaPermutesRoots z1 z2 z3 ∧
      xiTerminalZmS3IotaSwapsConjugates z1 z2 z3 ∧
      xiTerminalZmS3GeneratesS3 := by
  have hz2 :
      z2 = -((1 + 2 * y) + z1) / 2 + w / (2 * dRdz) := by
    calc
      z2 = ((z2 + z3) + (z2 - z3)) / 2 := by ring
      _ = (-((1 + 2 * y) + z1) + w / dRdz) / 2 := by rw [hsum, hdiff]
      _ = -((1 + 2 * y) + z1) / 2 + (w / dRdz) / 2 := by ring
      _ = -((1 + 2 * y) + z1) / 2 + w / (2 * dRdz) := by
        field_simp [hdRdz]
  have hz3 :
      z3 = -((1 + 2 * y) + z1) / 2 - w / (2 * dRdz) := by
    calc
      z3 = ((z2 + z3) - (z2 - z3)) / 2 := by ring
      _ = (-((1 + 2 * y) + z1) - w / dRdz) / 2 := by rw [hsum, hdiff]
      _ = -((1 + 2 * y) + z1) / 2 - (w / dRdz) / 2 := by ring
      _ = -((1 + 2 * y) + z1) / 2 - w / (2 * dRdz) := by
        field_simp [hdRdz]
  exact
    ⟨hz2, hz3,
      by
        simp [xiTerminalZmS3SigmaPermutesRoots, xiTerminalZmS3RootValue,
          xiTerminalZmS3SigmaIndex],
      by
        simp [xiTerminalZmS3IotaSwapsConjugates, xiTerminalZmS3RootValue,
          xiTerminalZmS3IotaIndex],
      xi_terminal_zm_s3_generates_s3⟩

end Omega.Zeta
