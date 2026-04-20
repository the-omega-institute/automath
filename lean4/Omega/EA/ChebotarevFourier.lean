import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.EA

open scoped BigOperators

/-- Primitive class count obtained by summing the primitive orbit weights in the congruence class
`c`. -/
noncomputable def chebotarevPrimitiveClassCount
    {α G : Type*} [Fintype α] [DecidableEq G]
    (orbitClass : α → G) (primitiveWeight : α → ℂ) (c : G) : ℂ :=
  ∑ a, if orbitClass a = c then primitiveWeight a else 0

/-- Character-twisted primitive count attached to the congruence labeling `orbitClass`. -/
noncomputable def chebotarevTwistedPrimitiveCount
    {α G Χ : Type*} [Fintype α]
    (eval : Χ → G → ℂ) (orbitClass : α → G) (primitiveWeight : α → ℂ) (χ : Χ) : ℂ :=
  ∑ a, eval χ (orbitClass a) * primitiveWeight a

/-- Finite-abelian Fourier recovery for the primitive class counts: expanding the twisted counts
termwise and applying the character orthogonality relation reconstructs the class-count formula.
`prop:kernel-chebotarev-fourier` -/
theorem paper_kernel_chebotarev_fourier
    {α G Χ : Type*} [Fintype α] [Fintype G] [CommGroup G] [DecidableEq G] [Fintype Χ]
    (eval : Χ → G → ℂ) (orbitClass : α → G) (primitiveWeight : α → ℂ)
    (horth : ∀ c d : G,
      ∑ χ, star (eval χ c) * eval χ d =
        if c = d then (Fintype.card G : ℂ) else 0) :
    ∀ c : G,
      chebotarevPrimitiveClassCount orbitClass primitiveWeight c =
        (1 / (Fintype.card G : ℂ)) *
          ∑ χ, star (eval χ c) *
            chebotarevTwistedPrimitiveCount eval orbitClass primitiveWeight χ := by
  intro c
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hone : (1 / (Fintype.card G : ℂ)) * (Fintype.card G : ℂ) = 1 := by
    rw [one_div, inv_mul_cancel₀ hcard]
  symm
  calc
    (1 / (Fintype.card G : ℂ)) *
        ∑ χ, star (eval χ c) *
          chebotarevTwistedPrimitiveCount eval orbitClass primitiveWeight χ
      =
        (1 / (Fintype.card G : ℂ)) *
          ∑ a, (∑ χ, star (eval χ c) * eval χ (orbitClass a)) * primitiveWeight a := by
            unfold chebotarevTwistedPrimitiveCount
            apply congrArg ((1 / (Fintype.card G : ℂ)) * ·)
            calc
              ∑ χ, star (eval χ c) * ∑ a, eval χ (orbitClass a) * primitiveWeight a
                  = ∑ χ, ∑ a,
                      star (eval χ c) * (eval χ (orbitClass a) * primitiveWeight a) := by
                      apply Finset.sum_congr rfl
                      intro χ hχ
                      rw [Finset.mul_sum]
              _ = ∑ a, ∑ χ,
                    star (eval χ c) * (eval χ (orbitClass a) * primitiveWeight a) := by
                    rw [Finset.sum_comm]
              _ = ∑ a,
                    (∑ χ, star (eval χ c) * eval χ (orbitClass a)) * primitiveWeight a := by
                    apply Finset.sum_congr rfl
                    intro a ha
                    calc
                      ∑ χ, star (eval χ c) * (eval χ (orbitClass a) * primitiveWeight a)
                          = ∑ χ, (star (eval χ c) * eval χ (orbitClass a)) * primitiveWeight a := by
                              apply Finset.sum_congr rfl
                              intro χ hχ
                              ring
                      _ = (∑ χ, star (eval χ c) * eval χ (orbitClass a)) * primitiveWeight a := by
                            rw [← Finset.sum_mul]
    _ =
        (1 / (Fintype.card G : ℂ)) *
          ∑ a, (if c = orbitClass a then (Fintype.card G : ℂ) else 0) * primitiveWeight a := by
            apply congrArg ((1 / (Fintype.card G : ℂ)) * ·)
            apply Finset.sum_congr rfl
            intro a ha
            simpa using congrArg (fun z => z * primitiveWeight a) (horth c (orbitClass a))
    _ = ∑ a, if orbitClass a = c then primitiveWeight a else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      by_cases h : orbitClass a = c
      · have hc : c = orbitClass a := h.symm
        calc
          (1 / (Fintype.card G : ℂ)) *
              ((if c = orbitClass a then (Fintype.card G : ℂ) else 0) * primitiveWeight a)
              = (1 / (Fintype.card G : ℂ)) * ((Fintype.card G : ℂ) * primitiveWeight a) := by
                  simp [hc]
          _ = ((1 / (Fintype.card G : ℂ)) * (Fintype.card G : ℂ)) * primitiveWeight a := by
                ring
          _ = primitiveWeight a := by rw [hone, one_mul]
          _ = if orbitClass a = c then primitiveWeight a else 0 := by simp [h]
      · have hc : c ≠ orbitClass a := by simpa [eq_comm] using h
        simp [h, hc]
    _ = chebotarevPrimitiveClassCount orbitClass primitiveWeight c := by
      rfl

end Omega.EA
