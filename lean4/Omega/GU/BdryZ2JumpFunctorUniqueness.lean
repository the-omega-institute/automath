import Omega.GU.BdryZ2JumpUniqueness

namespace Omega.GU

/-- Paper-facing packaging of the classification of `S_k → ℤˣ` into the trivial and sign
characters.
    thm:bdry-z2-jump-functor-uniqueness -/
theorem paper_bdry_z2_jump_functor_uniqueness {k : Nat} (hk : 3 ≤ k)
    (χ : Equiv.Perm (Fin k) →* ℤˣ) : χ = trivHom k ∨ χ = signHom k := by
  rcases paper_bdry_binary_jump_orientation_functor_uniqueness k hk χ with hχ | hχ
  · left
    simpa [trivHom] using hχ
  · right
    simpa [signHom] using hχ

end Omega.GU
