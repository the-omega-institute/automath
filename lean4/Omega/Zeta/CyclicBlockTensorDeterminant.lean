import Omega.Zeta.CyclicDet

namespace Omega.Zeta

/-- Paper-facing arithmetic form of the cyclic block tensor determinant
    exponent rewrite. The `gcd/lcm` decomposition fixes the common period
    `Nat.lcm n n'`, and then the determinant factor can be rewritten using
    `β = α^n` and `β' = (α')^n'`.
    cor:cyclic-block-tensor-determinant -/
theorem paper_cyclic_block_tensor_determinant
    (n n' : ℕ) (α α' β β' r : ℤ)
    (hβ : β = α ^ n) (hβ' : β' = α' ^ n') :
    (1 - (α * α' * r) ^ Nat.lcm n n') ^ Nat.gcd n n' =
      (1 - β ^ (Nat.lcm n n' / n) * β' ^ (Nat.lcm n n' / n') * r ^ Nat.lcm n n') ^
        Nat.gcd n n' := by
  have hα :
      α ^ Nat.lcm n n' = β ^ (Nat.lcm n n' / n) := by
    rw [hβ, ← pow_mul]
    rw [Nat.mul_div_cancel' (Nat.dvd_lcm_left n n')]
  have hα' :
      α' ^ Nat.lcm n n' = β' ^ (Nat.lcm n n' / n') := by
    rw [hβ', ← pow_mul]
    rw [Nat.mul_div_cancel' (Nat.dvd_lcm_right n n')]
  have hrewrite :
      (α * α' * r) ^ Nat.lcm n n' =
        β ^ (Nat.lcm n n' / n) * β' ^ (Nat.lcm n n' / n') * r ^ Nat.lcm n n' := by
    calc
      (α * α' * r) ^ Nat.lcm n n'
          = ((α * α') * r) ^ Nat.lcm n n' := by simp [mul_assoc]
      _ = (α * α') ^ Nat.lcm n n' * r ^ Nat.lcm n n' := by rw [mul_pow]
      _ = (α ^ Nat.lcm n n' * α' ^ Nat.lcm n n') * r ^ Nat.lcm n n' := by rw [mul_pow]
      _ = (β ^ (Nat.lcm n n' / n) * β' ^ (Nat.lcm n n' / n')) * r ^ Nat.lcm n n' := by
            rw [hα, hα']
      _ = β ^ (Nat.lcm n n' / n) * β' ^ (Nat.lcm n n' / n') * r ^ Nat.lcm n n' := by
            simp [mul_assoc]
  simp [hrewrite]

end Omega.Zeta
