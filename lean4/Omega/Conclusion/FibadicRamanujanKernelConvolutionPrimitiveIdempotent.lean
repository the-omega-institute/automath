import Mathlib.Tactic

namespace Omega.Conclusion

/-- Diagonal finite-character coefficients for the fibadic Ramanujan kernel model. -/
abbrev conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_coefficient
    (Depth : Type*) :=
  Depth → Rat

/-- Zero coefficient vector. -/
def conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_zero
    {Depth : Type*} :
    conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_coefficient Depth :=
  fun _ => 0

/-- The exact-depth Ramanujan kernel as one diagonal basis idempotent. -/
def conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_kernel
    {Depth : Type*} [DecidableEq Depth] (d : Depth) :
    conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_coefficient Depth :=
  fun e => if e = d then 1 else 0

/-- Diagonal convolution in the finite character basis. -/
def conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_convolution
    {Depth : Type*}
    (f g :
      conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_coefficient Depth) :
    conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_coefficient Depth :=
  fun e => f e * g e

lemma conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_rat_idempotent
    (x : Rat) (hx : x * x = x) : x = 0 ∨ x = 1 := by
  have h : x * (x - 1) = 0 := by
    nlinarith [hx]
  rcases mul_eq_zero.mp h with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)

/-- Paper-facing statement for
`thm:conclusion-fibadic-ramanujan-kernel-convolution-primitive-idempotent`. -/
def conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_statement : Prop :=
  ∀ {Depth : Type*} [Fintype Depth] [DecidableEq Depth] (d e : Depth),
    (∀ f : conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_coefficient Depth,
      conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_convolution
          (conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_kernel d) f =
        fun x => if x = d then f d else 0) ∧
    conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_convolution
        (conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_kernel d)
        (conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_kernel d) =
      conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_kernel d ∧
    (d ≠ e →
      conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_convolution
          (conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_kernel d)
          (conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_kernel e) =
        conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_zero) ∧
    (∀ f : conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_coefficient Depth,
      conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_convolution
          (conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_kernel d) f =
        conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_convolution f
          (conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_kernel d)) ∧
    (∀ p : conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_coefficient Depth,
      conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_convolution p p = p →
        conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_convolution p
            (conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_kernel d) = p →
          p = conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_zero ∨
            p = conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_kernel d)

/-- Paper label:
`thm:conclusion-fibadic-ramanujan-kernel-convolution-primitive-idempotent`. -/
theorem paper_conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent :
    conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_statement := by
  intro Depth _ _ d e
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro f
    funext x
    by_cases hx : x = d
    · subst hx
      simp [conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_convolution,
        conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_kernel]
    · simp [conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_convolution,
        conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_kernel, hx]
  · funext x
    by_cases hx : x = d
    · subst hx
      simp [conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_convolution,
        conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_kernel]
    · simp [conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_convolution,
        conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_kernel, hx]
  · intro hde
    funext x
    by_cases hxd : x = d
    · subst hxd
      simp [conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_convolution,
        conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_kernel,
        conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_zero, hde]
    · simp [conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_convolution,
        conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_kernel,
        conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_zero, hxd]
  · intro f
    funext x
    by_cases hx : x = d
    · subst hx
      simp [conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_convolution,
        conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_kernel]
    · simp [conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_convolution,
        conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_kernel, hx]
  · intro p hpidem hple
    have hp_d : p d * p d = p d := by
      simpa [conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_convolution]
        using congrFun hpidem d
    rcases
      conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_rat_idempotent
        (p d) hp_d with hzero | hone
    · left
      funext x
      by_cases hx : x = d
      · subst hx
        simp [conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_zero, hzero]
      · have hxcoord := congrFun hple x
        simp [conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_convolution,
          conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_kernel, hx] at hxcoord
        simpa [conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_zero]
          using hxcoord.symm
    · right
      funext x
      by_cases hx : x = d
      · subst hx
        simp [conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_kernel, hone]
      · have hxcoord := congrFun hple x
        simp [conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_convolution,
          conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_kernel, hx] at hxcoord
        simp [conclusion_fibadic_ramanujan_kernel_convolution_primitive_idempotent_kernel, hx,
          hxcoord.symm]

end Omega.Conclusion
